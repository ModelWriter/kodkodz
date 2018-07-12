package kodkod.engine.satlab;

import com.microsoft.z3.*;
import com.sun.deploy.util.ArrayUtil;
import com.sun.org.apache.xpath.internal.operations.Bool;
import kodkod.ast.*;
import kodkod.ast.operator.ExprOperator;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.visitor.AbstractVoidVisitor;
import kodkod.engine.bool.Int;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.util.ints.Ints;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class Z3Solver implements SATSolver {

    // Bit size for bit vectors
    private int BIT_SIZE = 8;

    private Context ctx;

    private Solver solver;

    private EnumSort UNIV;

    private FuncDecl univToInt = null;

    private Map<Expression, FuncDecl> funcDeclMap = new HashMap<>();
    private Map<Variable, Expr> variableExprMap = new HashMap<>();
    //private Map<Variable, Expression> variableDeclMap = new HashMap<>();
    //private Map<Expr, BoolExpr> exprBoolExprMap = new HashMap<>();

    private Status status = Status.SATISFIABLE;
    private Bounds bounds = null;
    private Instance instance = null;

    private int quantifierID;
    private int skolemID;

    private Set<Formula> unsatFormulaSet = new HashSet<>();
    private Set<Map.Entry<Relation, Tuple>> unsatTupleSet = new HashSet<>();

    private long solvingTime = 0;

    //default goal
    private Goal goal = null;

    private Set<Expr> possibleExprs = new HashSet<>();
    private Map<Expr, Map.Entry<Relation, Tuple>> exprTupleMap = new HashMap<>();
    private Map<BoolExpr, Formula> boolExprFormulaMap = new HashMap<>();

    private Map<BoolExpr, BoolExpr> assertionMap = new HashMap<>();

    public Z3Solver() {
        Global.setParameter("model.compact", "true");
        Global.setParameter("smt.mbqi", "true");
        Global.setParameter("smt.pull-nested-quantifiers", "true");
        Global.setParameter("smt.mbqi.trace", "true");

        HashMap<String, String> cfg = new HashMap<>();
        cfg.put("proof", "true");
        cfg.put("model", "true");

        ctx = new Context(cfg);
        goal = ctx.mkGoal(true, false, false);
    }

    public void setBitSize(int bitSize) {
        this.BIT_SIZE = bitSize;
    }

    public Status getStatus() {
        return status;
    }

    public long getSolvingTimeInMilis() {
        return solvingTime;
    }

    public Instance getInstance() {
        return instance;
    }

    public Set<Map.Entry<Relation, Tuple>> getUnsatTupleSet() {
        return unsatTupleSet;
    }

    public Set<Formula> getUnsatFormulaSet() {
        return unsatFormulaSet;
    }

    private void makeAssertions(Formula formula, Bounds bounds) {
        System.out.println();
        System.out.println("----- z3 -----");
        System.out.println();

        this.bounds = bounds;

        Map<String, Object> objectMap = new HashMap<>();
        Map<Object, Expr> objectExprMap = new HashMap<>();

        for (int i = 0; i < bounds.universe().size(); i++) {
            Object object = bounds.universe().atom(i);
            objectMap.put(object.toString(), object);
        }

        UNIV = ctx.mkEnumSort("univ", objectMap.keySet().toArray(new String[objectMap.keySet().size()]));

        for (Expr expr : UNIV.getConsts()) {
            Object object = objectMap.get(expr.toString());
            if (object == null)
                object = objectMap.get(expr.toString().substring(1, expr.toString().length() - 1));
            objectExprMap.put(object, expr);
        }

        bounds.relations().forEach(relation -> {
            Sort[] sorts = new Sort[relation.arity()];
            for (int i = 0; i < sorts.length; i++) {
                sorts[i] = UNIV;
            }
            FuncDecl funcDecl = ctx.mkFuncDecl(relation.name(), sorts, ctx.mkBoolSort());
            funcDeclMap.put(relation, funcDecl);

            bounds.lowerBounds().get(relation).forEach(tuple -> {
                Expr[] exprs = new Expr[tuple.arity()];
                for (int i = 0; i < exprs.length; i++) {
                    exprs[i] = objectExprMap.get(tuple.atom(i));
                }
                goal.add((BoolExpr) ctx.mkApp(funcDecl, exprs));
            });

            bounds.universe().factory().allOf(relation.arity()).forEach(tuple -> {
                Expr[] exprs = new Expr[tuple.arity()];
                for (int i = 0; i < exprs.length; i++) {
                    exprs[i] = objectExprMap.get(tuple.atom(i));
                }
                BoolExpr expr = (BoolExpr) ctx.mkApp(funcDecl, exprs);
                possibleExprs.add(expr);
                exprTupleMap.put(expr, new AbstractMap.SimpleEntry<>(relation, tuple));
                if (!bounds.upperBound(relation).contains(tuple))
                    goal.add(ctx.mkNot(expr));
            });
        });

        if (objectExprMap.entrySet().stream().anyMatch(e -> e.getKey() instanceof Integer)) {
            FuncDecl intsFuncDecl = ctx.mkFuncDecl("Ints", new Sort[] {UNIV}, ctx.mkBoolSort());
            funcDeclMap.put(Relation.INTS, intsFuncDecl);

            univToInt = ctx.mkFuncDecl("toInt", UNIV, ctx.mkBitVecSort(BIT_SIZE));

            objectExprMap.forEach(((o, expr) -> {
                if (o instanceof Integer) {
                    goal.add((BoolExpr) ctx.mkApp(intsFuncDecl, expr));
                    goal.add(ctx.mkEq(ctx.mkApp(univToInt, expr), ctx.mkBV((Integer) o, BIT_SIZE)));
                }
                else {
                    goal.add(ctx.mkNot((BoolExpr) ctx.mkApp(intsFuncDecl, expr)));
                    goal.add(ctx.mkEq(ctx.mkApp(univToInt, expr), ctx.mkBV(0, BIT_SIZE)));
                }
            }));
        }

        boolExprFormulaMap = separateFormula(formula).stream()
                .collect(Collectors.toMap(
                        this::convert
                        , f -> f
                        , (a, b) -> a));

        boolExprFormulaMap.keySet().forEach(goal::add);

        //Tactics
        Tactic t_qe = ctx.mkTactic("qe");
        Tactic t_default = ctx.mkTactic("snf");
        solver = ctx.mkSolver();
        Params p = ctx.mkParams();
        p.add("mbqi", true);
        p.add("pull-nested-quantifiers", true);
        solver.setParameters(p);

        // Pattern to find all quantifiers
        Pattern pattern = Pattern.compile("([(][a-zA-Z0-9!]+( univ)[)])");

        for (BoolExpr original : goal.getFormulas()) {
            Goal singletonGoal = ctx.mkGoal(true, false, false);
            singletonGoal.add(original);
            ApplyResult qe_ar = t_default.apply(singletonGoal);

            BoolExpr[] newOnes = qe_ar.getSubgoals()[0].getFormulas();
            Formula f = boolExprFormulaMap.get(original);
            if (f != null) {
                System.out.println("kodkod: " + f);
                System.out.println("z3:");
                System.out.println(original);
            }
            for (int i = 0; i < newOnes.length; i++) {
                BoolExpr e = newOnes[i];
                int forallCount = 0;
                Matcher matcher = pattern.matcher(e.getSExpr());

                while (matcher.find())
                    forallCount++;

                System.out.println("snf z3:");
                System.out.println(newOnes[i]);
                System.out.println();
                System.out.println("Quantifiers: " + forallCount);
                System.out.println();
                if (forallCount < 2) {
                    BoolExpr boolExpr = ctx.mkBoolConst("! " + e.toString());
                    assertionMap.put(boolExpr, original);
                    solver.assertAndTrack(e, boolExpr);
                } else {
                    Goal ge_goal = ctx.mkGoal(true, false, false);

                    ge_goal.add(e);

                    ApplyResult ar = t_qe.apply(ge_goal);

                    for (BoolExpr b : ar.getSubgoals()[0].getFormulas()) {
                        BoolExpr boolExpr = ctx.mkBoolConst("! " + b.toString());
                        assertionMap.put(boolExpr, original);
                        solver.assertAndTrack(b, boolExpr);
                    }
                }
            }

        }
        //end of tactics application

        System.out.println("----------------After Tactics----------------------");
        System.out.println(solver);
        System.out.println("---------------------------------------------------");

        System.out.println();
        System.out.println();
    }

    public Iterator<Instance> solveAll(Formula formula, Bounds bounds) {
        makeAssertions(formula, bounds);

        return new Iterator<Instance>() {
            @Override
            public boolean hasNext() {
                return status.equals(Status.SATISFIABLE);
            }

            @Override
            public Instance next() {

                System.out.println(solver);
                System.out.println("---------------------------------------------------");

                solveThis(bounds);

                if (status.equals(Status.SATISFIABLE)) {
                    solver.add(ctx.mkNot(ctx.mkAnd(possibleExprs.stream()
                            .filter(expr -> expr instanceof BoolExpr && solver.getModel().eval(expr, true).equals(ctx.mkTrue()))
                            .map(expr -> (BoolExpr) expr).toArray(BoolExpr[]::new))));
                }

                return instance;
            }
        };
    }

    public boolean solve(Formula formula, Bounds bounds) {
        makeAssertions(formula, bounds);

        solveThis(bounds);

        return status == Status.SATISFIABLE;
    }

    private void solveThis(Bounds bounds){

        long beginningTime = System.currentTimeMillis();
        status = solver.check();
        solvingTime = System.currentTimeMillis() - beginningTime;

        System.out.println(solvingTime + " ms");

        switch (status) {
            case SATISFIABLE:
                Set<Expr> reasonedExprs = possibleExprs.stream()
                        .filter(expr -> solver.getModel().eval(expr, true).equals(ctx.mkTrue()))
                        .collect(Collectors.toSet());

                System.out.println("Sat");
                reasonedExprs.forEach(System.out::println);
                System.out.println();
                possibleExprs.forEach(e -> System.out.println(e + " = " + solver.getModel().eval(e, true)));
                System.out.println();
                System.out.println(solver.getModel());

                this.instance = new Instance(bounds.universe());

                Map<Relation, Set<Tuple>> relationTuplesMap = new HashMap<>();

                reasonedExprs.forEach(expr -> {
                    Map.Entry<Relation, Tuple> entry = exprTupleMap.get(expr);
                    relationTuplesMap.computeIfAbsent(entry.getKey(), r -> new HashSet<>()).add(entry.getValue());
                });

                relationTuplesMap.forEach((relation, tuples) -> {
                    instance.add(relation, bounds.universe().factory().setOf(tuples));
                });

                for (int i : bounds.ints().toArray()) {
                    instance.add(i, bounds.universe().factory().setOf(i));
                }

                System.out.println(instance);
                break;
            case UNSATISFIABLE:
                System.out.println("Unsat core:");
                Arrays.stream(solver.getUnsatCore()).forEach(System.out::println);

                Map<String, Formula> boolExprStrToFormula = new HashMap<>();
                boolExprFormulaMap.forEach((b, f) -> boolExprStrToFormula.put(b.toString(), f));

                unsatFormulaSet.clear();
                unsatFormulaSet.clear();

                Arrays.stream(solver.getUnsatCore()).forEach(boolExpr -> {
                    BoolExpr assertion = assertionMap.get(boolExpr);
                    if (exprTupleMap.containsKey(assertion)) {
                        unsatTupleSet.add(exprTupleMap.get(assertion));
                    }
                    else if (boolExprFormulaMap.containsKey(assertion)) {
                        unsatFormulaSet.add(boolExprFormulaMap.get(assertion));
                    }
                });

                this.instance = null;
                break;
            case UNKNOWN:
                System.out.println("Unknown");
                break;
        }
    }

    private Set<Formula> separateFormula(Formula formula) {
        if (formula instanceof BinaryFormula && ((BinaryFormula) formula).op().equals(FormulaOperator.AND)) {
            Set<Formula> formulaSet = new HashSet<>();
            formulaSet.addAll(separateFormula(((BinaryFormula) formula).left()));
            formulaSet.addAll(separateFormula(((BinaryFormula) formula).right()));
            return formulaSet;
        }
        if (formula instanceof NaryFormula && ((NaryFormula) formula).op().equals(FormulaOperator.AND)) {
            Set<Formula> formulaSet = new HashSet<>();
            ((NaryFormula) formula).iterator().forEachRemaining(f -> {
                formulaSet.addAll(separateFormula(f));
            });
            return formulaSet;
        }
        return Collections.singleton(formula);
    }

    private static final String quantifierPrefix = "q!";
    private static final String skolemPrefix = "s!";

    // private Formula currentFormula = null;

    int count = 0;

    private BoolExpr convert(Formula node) {
        // currentFormula = node;
        count++;
        cardinalityFuncMap.clear();
        variableExprMap.clear();
        return visit(node, 0, new Expr[0]);
    }

    private BoolExpr visit(Node node, int depth, Expr[] exprs) {
        if (node instanceof Relation) {
            return (BoolExpr) ctx.mkApp(funcDeclMap.get(node), exprs);
        }
        else if (node instanceof ConstantExpression) {
            if (node == Relation.IDEN) {
                return ctx.mkEq(exprs[0], exprs[1]);
            }
            if (node == Relation.NONE) {
                return ctx.mkFalse();
            }
            if (node == Relation.UNIV) {
                return exprs.length == 1 ? ctx.mkTrue() : ctx.mkFalse();
            }

            FuncDecl funcDecl = funcDeclMap.get(node);
            return funcDecl == null ? ctx.mkFalse() : (BoolExpr) ctx.mkApp(funcDecl, exprs);
        }
        else if (node instanceof Variable) {
            return ctx.mkEq(variableExprMap.get(node), exprs[0]);
        }
        else if (node instanceof UnaryExpression) {
            UnaryExpression unaryExpression = (UnaryExpression) node;
            switch (unaryExpression.op()) {
                case TRANSPOSE:
                    return visit(unaryExpression.expression(), depth, new Expr[] {exprs[1], exprs[0]});
                case REFLEXIVE_CLOSURE:
                    Expression ex = unaryExpression.expression();
                    while (ex instanceof BinaryExpression && ((BinaryExpression) ex).op().equals(ExprOperator.JOIN)) {
                        ex = ((BinaryExpression) ex).right();
                    }

                    int loopCount =  UNIV.getConsts().length - 1;

                    if (ex.equals(Relation.NONE)) {
                        loopCount = 0;
                    }
                    else if (ex instanceof Relation) {
                        loopCount = (int) (bounds.upperBound((Relation) ex).stream()
                                .map(t -> t.atom(t.arity() - 1))
                                .distinct().count()) - 1;
                    }

                    Expression unionExpr = Relation.IDEN;
                    for (int i = 0; i < loopCount; i++) {
                        unionExpr = Relation.IDEN.union(unaryExpression.expression().join(unionExpr));
                    }

                    return visit(unionExpr, depth, exprs);
                case CLOSURE:
                    ex = unaryExpression.expression();
                    while (ex instanceof BinaryExpression && ((BinaryExpression) ex).op().equals(ExprOperator.JOIN)) {
                        ex = ((BinaryExpression) ex).right();
                    }

                    loopCount =  UNIV.getConsts().length - 1;

                    if (ex.equals(Relation.NONE)) {
                        loopCount = 0;
                    }
                    else if (ex instanceof Relation) {
                        loopCount = (int) (bounds.upperBound((Relation) ex).stream()
                                .map(t -> t.atom(t.arity() - 1))
                                .distinct().count()) - 1;
                    }

                    unionExpr = Relation.IDEN;
                    for (int i = 0; i < loopCount; i++) {
                        unionExpr = Relation.IDEN.union(unaryExpression.expression().join(unionExpr));
                    }

                    if (unionExpr instanceof BinaryExpression && ((BinaryExpression) unionExpr).op().equals(ExprOperator.UNION))
                        return visit(((BinaryExpression) unionExpr).right(), depth, exprs);
                    else {
                        return ctx.mkFalse();
                    }
            }
        }
        else if (node instanceof BinaryExpression) {
            BinaryExpression binaryExpression = (BinaryExpression) node;
            switch (binaryExpression.op()) {
                case JOIN:
                    Expr expr = ctx.mkConst("x!" + depth, UNIV);

                    Expression leftExpression = binaryExpression.left();
                    Expression rightExpression = binaryExpression.right();

                    Expr[] leftExprs = new Expr[leftExpression.arity()];

                    System.arraycopy(exprs, 0, leftExprs, 0, leftExprs.length - 1);
                    leftExprs[leftExprs.length - 1] = expr;

                    Expr[] rightExprs = new Expr[rightExpression.arity()];

                    rightExprs[0] = expr;
                    System.arraycopy(exprs, exprs.length - rightExprs.length + 1, rightExprs, 1, rightExprs.length - 1);

                    if (leftExpression instanceof Variable) {
                        rightExprs[0] = variableExprMap.get(leftExpression);
                        return visit(rightExpression, depth + 1, rightExprs);
                    }
                    else if (rightExpression instanceof Variable) {
                        leftExprs[leftExprs.length - 1] = variableExprMap.get(rightExpression);
                        return visit(leftExpression, depth + 1, leftExprs);
                    }

                    return ctx.mkExists(new Expr[] {expr}
                            , ctx.mkAnd(visit(leftExpression, depth + 1, leftExprs)
                                    , visit(rightExpression, depth + 1, rightExprs))
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), ctx.mkSymbol(skolemPrefix + skolemID++));
                case UNION:
                    return ctx.mkOr(visit(binaryExpression.left(), depth, exprs), visit(binaryExpression.right(), depth, exprs));
                case INTERSECTION:
                    return ctx.mkAnd(visit(binaryExpression.left(), depth, exprs), visit(binaryExpression.right(), depth, exprs));
                case PRODUCT:
                    leftExpression = binaryExpression.left();
                    rightExpression = binaryExpression.right();

                    leftExprs = new Expr[leftExpression.arity()];
                    System.arraycopy(exprs, 0, leftExprs, 0, leftExprs.length);

                    rightExprs = new Expr[rightExpression.arity()];
                    System.arraycopy(exprs, leftExpression.arity(), rightExprs, 0, rightExprs.length);

                    return ctx.mkAnd(visit(leftExpression, depth, leftExprs), visit(rightExpression, depth, rightExprs));
                case DIFFERENCE:
                    return ctx.mkAnd(visit(binaryExpression.left(), depth, exprs), ctx.mkNot(visit(binaryExpression.right(), depth, exprs)));
                case OVERRIDE:
                    BoolExpr boolExpr = visit(binaryExpression.right(), depth, exprs);
                    return (BoolExpr) ctx.mkITE(boolExpr, ctx.mkTrue(), visit(binaryExpression.left(), depth, exprs));
            }
        }
        else if (node instanceof NaryExpression) {
            NaryExpression naryExpression = (NaryExpression) node;

            switch (naryExpression.op()) {
                case UNION:
                    BoolExpr[] boolExprs = new BoolExpr[naryExpression.size()];
                    for (int i = 0; i < boolExprs.length; i++) {
                        boolExprs[i] = visit(naryExpression.child(i), depth, exprs);
                    }
                    return ctx.mkOr(boolExprs);
                case PRODUCT:
                    boolExprs = new BoolExpr[naryExpression.size()];
                    for (int i = 0; i < boolExprs.length; i++) {
                        int start = 0;

                        for (int j = 0; j < i; j++)
                            start += naryExpression.child(i - 1).arity();

                        Expression expression = naryExpression.child(i);
                        Expr[] exprs1 = new Expr[expression.arity()];

                        System.arraycopy(exprs, start, exprs1, 0, exprs1.length);

                        boolExprs[i] = visit(expression, depth, exprs1);
                    }
                    return ctx.mkAnd(boolExprs);
                case INTERSECTION:
                    boolExprs = new BoolExpr[naryExpression.size()];
                    for (int i = 0; i < boolExprs.length; i++) {
                        boolExprs[i] = visit(naryExpression.child(i), depth, exprs);
                    }
                    return ctx.mkAnd(boolExprs);
                case OVERRIDE:
                    if (naryExpression.size() <= 0)
                        return ctx.mkFalse();

                    BoolExpr boolExpr = visit(naryExpression.child(0), depth, exprs);
                    for (int i = 1; i < naryExpression.size(); i++) {
                        BoolExpr temp = visit(naryExpression.child(i), depth, exprs);
                        boolExpr = (BoolExpr) ctx.mkITE(temp, ctx.mkTrue(), boolExpr);
                    }

                    return boolExpr;
            }
        }
        else if (node instanceof NotFormula) {
            NotFormula notFormula = (NotFormula) node;
            return ctx.mkNot(visit(notFormula.formula(), depth, exprs));
        }
        else if (node instanceof ComparisonFormula) {
            ComparisonFormula comparisonFormula = (ComparisonFormula) node;
            switch (comparisonFormula.op()) {
                case EQUALS:
                    Expr[] exprs1;
                    if (comparisonFormula.left() instanceof Variable) {
                        if (comparisonFormula.right() instanceof Variable) {
                            return ctx.mkEq(variableExprMap.get(comparisonFormula.left()), variableExprMap.get(comparisonFormula.right()));
                        }
                        else {
                            exprs1 = new Expr[comparisonFormula.left().arity()];
                            exprs1[0] = variableExprMap.get(comparisonFormula.left());
                            return visit(comparisonFormula.right(), depth, exprs1);
                        }
                    }
                    else if (comparisonFormula.right() instanceof Variable) {
                        exprs1 = new Expr[comparisonFormula.right().arity()];
                        exprs1[0] = variableExprMap.get(comparisonFormula.right());
                        return visit(comparisonFormula.left(), depth, exprs1);
                    }

                    exprs1 = new Expr[comparisonFormula.left().arity()];
                    for (int i = 0; i < exprs1.length; i++) {
                        exprs1[i] = ctx.mkConst("x!" + (depth + i), UNIV);
                    }

                    BoolExpr left = visit(comparisonFormula.left(), exprs1.length + depth, exprs1);
                    BoolExpr right = visit(comparisonFormula.right(), exprs1.length + depth, exprs1);

                    return ctx.mkForall(exprs1, ctx.mkEq(left, right)
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
                case SUBSET:
                    if (comparisonFormula.left() instanceof Variable) {
                        if (comparisonFormula.right() instanceof Variable) {
                            return ctx.mkEq(variableExprMap.get(comparisonFormula.left()), variableExprMap.get(comparisonFormula.right()));
                        }
                        else {
                            exprs1 = new Expr[comparisonFormula.left().arity()];
                            exprs1[0] = variableExprMap.get(comparisonFormula.left());
                            return visit(comparisonFormula.right(), depth, exprs1);
                        }
                    }
                    else if (comparisonFormula.right() instanceof Variable) {
                        exprs1 = new Expr[comparisonFormula.right().arity()];
                        exprs1[0] = variableExprMap.get(comparisonFormula.right());
                        return visit(comparisonFormula.left(), depth, exprs1);
                    }

                    exprs1 = new Expr[comparisonFormula.left().arity()];
                    for (int i = 0; i < exprs1.length; i++) {
                        exprs1[i] = ctx.mkConst("x!" + (i + depth), UNIV);
                    }
                    return ctx.mkForall(exprs1
                            , ctx.mkImplies(visit(comparisonFormula.left(), exprs1.length + depth, exprs1)
                                    , visit(comparisonFormula.right(), exprs1.length + depth, exprs1))
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
            }
        }
        else if (node instanceof BinaryFormula) {
            BinaryFormula binaryFormula = (BinaryFormula) node;
            switch (binaryFormula.op()) {
                case IMPLIES:
                    return ctx.mkImplies(visit(binaryFormula.left(), depth, exprs), visit(binaryFormula.right(), depth, exprs));
                case IFF:
                    BoolExpr left = visit(binaryFormula.left(), depth, exprs);
                    BoolExpr right = visit(binaryFormula.right(), depth, exprs);
                    return ctx.mkEq(left, right);
                case OR:
                    return ctx.mkOr(visit(binaryFormula.left(), depth, exprs), visit(binaryFormula.right(), depth, exprs));
                case AND:
                    return ctx.mkAnd(visit(binaryFormula.left(), depth, exprs), visit(binaryFormula.right(), depth, exprs));
            }
        }
        else if (node instanceof NaryFormula) {
            NaryFormula naryFormula = (NaryFormula) node;
            switch (naryFormula.op()) {
                case AND:
                    BoolExpr[] boolExprs = new BoolExpr[naryFormula.size()];
                    for (int i = 0; i < boolExprs.length; i++) {
                        boolExprs[i] = visit(naryFormula.child(i), depth, exprs);
                    }
                    return ctx.mkAnd(boolExprs);
                case OR:
                    boolExprs = new BoolExpr[naryFormula.size()];
                    for (int i = 0; i < boolExprs.length; i++) {
                        boolExprs[i] = visit(naryFormula.child(i), depth, exprs);
                    }
                    return ctx.mkOr(boolExprs);
            }
        }
        else if (node instanceof MultiplicityFormula) {
            MultiplicityFormula multiplicityFormula = (MultiplicityFormula) node;
            switch (multiplicityFormula.multiplicity()) {
                case SOME:
                    Expr[] exprs1 = new Expr[multiplicityFormula.expression().arity()];
                    for (int i = 0; i < exprs1.length; i++) {
                        exprs1[i] = ctx.mkConst("x!" + (i + depth), UNIV);
                    }
                    return ctx.mkExists(exprs1
                            , visit(multiplicityFormula.expression(), exprs1.length + depth, exprs1)
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), ctx.mkSymbol(skolemPrefix + skolemID++));
                case NO:
                    exprs1 = new Expr[multiplicityFormula.expression().arity()];
                    if (multiplicityFormula.expression() instanceof IntToExprCast) {
                        for (int i = 0; i < exprs1.length; i++) {
                            exprs1[i] = ctx.mkBVConst("i!" + (i + depth), BIT_SIZE);
                        }
                    }
                    else {
                        for (int i = 0; i < exprs1.length; i++) {
                            exprs1[i] = ctx.mkConst("x!" + (i + depth), UNIV);
                        }
                    }

                    return ctx.mkNot(ctx.mkExists(exprs1
                            , visit(multiplicityFormula.expression(), exprs1.length + depth, exprs1)
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), ctx.mkSymbol(skolemPrefix + skolemID++)));
                case ONE:
                    exprs1 = new Expr[multiplicityFormula.expression().arity()];
                    for (int i = 0; i < exprs1.length; i++) {
                        exprs1[i] = ctx.mkConst("y!" + (i + depth), UNIV);
                    }
                    Expr[] exprs2 = new Expr[multiplicityFormula.expression().arity()];
                    for (int i = 0; i < exprs2.length; i++) {
                        exprs2[i] = ctx.mkConst("z!" + (i + depth), UNIV);
                    }
                    BoolExpr[] eqs = new BoolExpr[exprs1.length];
                    for (int i = 0; i < eqs.length; i++) {
                        eqs[i] = ctx.mkEq(exprs1[i], exprs2[i]);
                    }

                    Expr[] allExprs = new Expr[exprs1.length + exprs2.length];
                    System.arraycopy(exprs1, 0, allExprs, 0, exprs1.length);
                    System.arraycopy(exprs2, 0, allExprs, exprs1.length, exprs2.length);

                    Quantifier lone = ctx.mkForall(allExprs
                            , ctx.mkImplies(
                                    ctx.mkAnd(visit(multiplicityFormula.expression(), depth, exprs1)
                                            , visit(multiplicityFormula.expression(), depth, exprs2))
                                    , ctx.mkAnd(eqs))
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
                    Quantifier some = ctx.mkExists(exprs1, visit(multiplicityFormula.expression(), depth, exprs1)
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), ctx.mkSymbol(skolemPrefix + skolemID++));

                    return ctx.mkAnd(some, lone);
                case LONE:
                    exprs1 = new Expr[multiplicityFormula.expression().arity()];
                    for (int i = 0; i < exprs1.length; i++) {
                        exprs1[i] = ctx.mkConst("y!" + (i + depth), UNIV);
                    }
                    exprs2 = new Expr[multiplicityFormula.expression().arity()];
                    for (int i = 0; i < exprs1.length; i++) {
                        exprs2[i] = ctx.mkConst("z!" + (i + depth), UNIV);
                    }
                    eqs = new BoolExpr[exprs1.length];
                    for (int i = 0; i < eqs.length; i++) {
                        eqs[i] = ctx.mkEq(exprs1[i], exprs2[i]);
                    }

                    allExprs = new Expr[exprs1.length + exprs2.length];
                    System.arraycopy(exprs1, 0, allExprs, 0, exprs1.length);
                    System.arraycopy(exprs2, 0, allExprs, exprs1.length, exprs2.length);

                    return ctx.mkForall(allExprs
                            , ctx.mkImplies(
                                    ctx.mkAnd(visit(multiplicityFormula.expression(), depth, exprs1)
                                            , visit(multiplicityFormula.expression(), depth, exprs2))
                                    , ctx.mkAnd(eqs))
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
            }
        }
        else if (node instanceof QuantifiedFormula) {
            QuantifiedFormula quantifiedFormula = (QuantifiedFormula) node;
            int exprsSize = quantifiedFormula.decls().size();

            Expr[] exprs1 = new Expr[exprsSize];
            BoolExpr[] ands = new BoolExpr[exprsSize];

            for (int i = 0; i < exprsSize; i++) {
                Decl decl = quantifiedFormula.decls().get(i);
                exprs1[i] = ctx.mkConst(decl.variable().name()/*"x" + (i + depth)*/, UNIV);
                variableExprMap.put(decl.variable(), exprs1[i]);
                //variableDeclMap.put(decl.variable(), decl.expression());
                //exprBoolExprMap.put(exprs1[i], ands[i]);
            }
            for (int i = 0; i < exprsSize; i++) {
                Decl decl = quantifiedFormula.decls().get(i);
                ands[i] = visit(decl.variable().in(decl.expression()), depth + exprsSize, exprs);
            }

            switch (quantifiedFormula.quantifier()) {
                case ALL:
                    return ctx.mkForall(exprs1
                            , ctx.mkImplies(ctx.mkAnd(ands)
                                    , visit(quantifiedFormula.formula(), depth + exprs1.length, exprs1))
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
                case SOME:
                    return ctx.mkExists(exprs1
                            , ctx.mkAnd(ctx.mkAnd(ands)
                                    , visit(quantifiedFormula.formula(), depth + exprs1.length, exprs1))
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), ctx.mkSymbol(skolemPrefix + skolemID++));
            }
        }
        if (node instanceof ConstantFormula) {
            ConstantFormula constantFormula = (ConstantFormula) node;
            if (constantFormula.booleanValue()) {
                return ctx.mkTrue();
            }
            else {
                return ctx.mkFalse();
            }
        }
        else if (node instanceof IntComparisonFormula) {
            IntComparisonFormula intComparisonFormula = (IntComparisonFormula) node;
            switch (intComparisonFormula.op()) {
                case EQ:
                    return ctx.mkEq(visitIntExpression(intComparisonFormula.left(), depth, exprs)
                            , visitIntExpression(intComparisonFormula.right(), depth, exprs));
                case GT:
                    return ctx.mkBVSGT(visitIntExpression(intComparisonFormula.left(), depth, exprs)
                            , visitIntExpression(intComparisonFormula.right(), depth, exprs));
                case LT:
                    return ctx.mkBVSLT(visitIntExpression(intComparisonFormula.left(), depth, exprs)
                            , visitIntExpression(intComparisonFormula.right(), depth, exprs));
                case GTE:
                    return ctx.mkBVSGE(visitIntExpression(intComparisonFormula.left(), depth, exprs)
                            , visitIntExpression(intComparisonFormula.right(), depth, exprs));
                case LTE:
                    return ctx.mkBVSLE(visitIntExpression(intComparisonFormula.left(), depth, exprs)
                            , visitIntExpression(intComparisonFormula.right(), depth, exprs));
            }
        }
        else if (node instanceof IntToExprCast) {
            IntToExprCast intToExprCast = (IntToExprCast) node;
            switch (intToExprCast.op()) {
                case INTCAST:
                    // TODO: Implement this.
                    return ctx.mkTrue();
                case BITSETCAST:
                    // TODO: Implement this.
                    return ctx.mkTrue();
            }
        }
        else if (node instanceof IfExpression) {
            IfExpression ifExpression = (IfExpression) node;
            return ctx.mkAnd(ctx.mkImplies(visit(ifExpression.condition(), depth, exprs), visit(ifExpression.thenExpr(), depth, exprs))
                    , ctx.mkImplies(visit(ifExpression.condition().not(), depth, exprs), visit(ifExpression.elseExpr(), depth, exprs)));
        }
        else if (node instanceof RelationPredicate) {
            RelationPredicate relationPredicate = (RelationPredicate) node;
            return visit(relationPredicate.toConstraints(), depth, exprs);
        }

        return ctx.mkFalse();
    }

    private Map<String, FuncDecl> cardinalityFuncMap = new HashMap<>();
    // private Map<String, FuncDecl> orderFuncMap = new HashMap<>();

    private BitVecExpr visitIntExpression(IntExpression node, int depth, Expr[] exprs) {
        if (node instanceof kodkod.ast.IntConstant) {
            IntConstant intConstant = (IntConstant) node;
            return ctx.mkBV(intConstant.value(), BIT_SIZE);
        }
        else if (node instanceof ExprToIntCast) {
            ExprToIntCast exprToIntCast = (ExprToIntCast) node;

            switch (exprToIntCast.op()) {
                case CARDINALITY:
                    Set<Variable> variables = new HashSet<>();
                    AbstractVoidVisitor abstractVoidVisitor = new AbstractVoidVisitor() {
                        private Set<Node> visitedNodes = new HashSet<>();

                        @Override
                        protected boolean visited(Node n) {
                            if (visitedNodes.contains(n))
                                return true;
                            visitedNodes.add(n);
                            return false;
                        }

                        @Override
                        public void visit(Variable variable) {
                            variables.add(variable);
                            super.visit(variable);
                        }
                    };

                    count++;

                    abstractVoidVisitor.visit(exprToIntCast);
                    Set<Expr> usedExprs = variables.stream()
                            .filter(e -> variableExprMap.containsKey(e))
                            .map(variableExprMap::get)
                            .collect(Collectors.toSet());

                    exprs = usedExprs.toArray(new Expr[usedExprs.size()]);

                    if (cardinalityFuncMap.containsKey(exprToIntCast.toString()))
                        return (BitVecExpr) cardinalityFuncMap.get(exprToIntCast.toString()).apply(exprs);

                    Expression expression = exprToIntCast.expression();

                    Sort[] sorts = new Sort[exprs.length];
                    Arrays.fill(sorts, UNIV);
                    FuncDecl cardFunc = ctx.mkFuncDecl("#[" + exprToIntCast.expression().toString() + "]" + count, sorts, ctx.mkBitVecSort(BIT_SIZE));

                    int parameterSize = exprs.length + expression.arity();

                    Sort[] ordSorts = new Sort[parameterSize];
                    Arrays.fill(ordSorts, UNIV);
                    FuncDecl ordFunc = ctx.mkFuncDecl("ord[" + exprToIntCast.expression().toString() + "]" + count, ordSorts, ctx.mkBitVecSort(BIT_SIZE));

                    BoolExpr eqZero = ctx.mkIff(ctx.mkEq(cardFunc.apply(exprs), ctx.mkBV(0, BIT_SIZE))
                            , visit(expression.no(), depth + 1, exprs));

                    if (exprs.length > 0) {
                        eqZero = ctx.mkForall(exprs, eqZero
                                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
                    }

                    Expr[] exprsOrd = new Expr[ordSorts.length];
                    System.arraycopy(exprs, 0, exprsOrd, 0, exprs.length);
                    for (int i = exprs.length; i < exprsOrd.length; i++) {
                        exprsOrd[i] = ctx.mkConst("x!" + (i + depth), UNIV);
                    }

                    BoolExpr ordExpr = ctx.mkForall(exprsOrd
                            , ctx.mkImplies(visit(expression, depth + exprsOrd.length, Arrays.copyOfRange(exprsOrd, exprs.length, exprsOrd.length))
                                    , ctx.mkAnd(ctx.mkBVSLE(ctx.mkBV(1, BIT_SIZE), (BitVecExpr) ordFunc.apply(exprsOrd))
                                            , ctx.mkBVSLE((BitVecExpr) ordFunc.apply(exprsOrd)
                                                    , (BitVecExpr) cardFunc.apply(Arrays.copyOfRange(exprsOrd, 0, exprs.length)))))
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

                    Expr[] exprsInv = new Expr[exprs.length + 1];
                    System.arraycopy(exprs, 0, exprsInv, 0, exprs.length);
                    exprsInv[exprsInv.length - 1] = ctx.mkBVConst("i!" + (depth + 1), BIT_SIZE);

                    Expr[] outExpr = new Expr[expression.arity()];
                    System.arraycopy(exprsOrd, exprs.length, outExpr, 0, outExpr.length);

                    BoolExpr invExpr = ctx.mkForall(exprsInv,
                            ctx.mkImplies(ctx.mkAnd(ctx.mkBVSLE(ctx.mkBV(1, BIT_SIZE), (BitVecExpr) exprsInv[exprsInv.length - 1])
                                            , ctx.mkBVSLE((BitVecExpr) exprsInv[exprsInv.length - 1], (BitVecExpr) cardFunc.apply(exprs)))
                                    , ctx.mkExists(outExpr, ctx.mkAnd(
                                            ctx.mkEq(ordFunc.apply(exprsOrd), exprsInv[exprsInv.length - 1])
                                            , visit(expression, depth + exprsOrd.length, outExpr))
                                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null))
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

                    Expr[] exprsOneToOne = new Expr[exprsOrd.length * 2 - exprs.length];
                    System.arraycopy(exprs, 0, exprsOneToOne, 0, exprs.length);
                    for (int i = exprs.length; i < exprsOneToOne.length; i++) {
                        exprsOneToOne[i] = ctx.mkConst("x!" + (i + depth), UNIV);
                    }

                    BoolExpr[] ands = new BoolExpr[exprsOrd.length - exprs.length];
                    for (int i = 0; i < ands.length; i++) {
                        ands[i] = ctx.mkEq(exprsOneToOne[i + exprs.length], exprsOneToOne[i + exprs.length + ands.length]);
                    }

                    Expr[] exprsFirst = new Expr[exprsOrd.length];
                    System.arraycopy(exprs, 0, exprsFirst, 0, exprs.length);
                    System.arraycopy(exprsOneToOne, exprs.length, exprsFirst, exprs.length, exprsFirst.length - exprs.length);

                    Expr[] exprsSecond = new Expr[exprsOrd.length];
                    System.arraycopy(exprs, 0, exprsSecond, 0, exprs.length);
                    System.arraycopy(exprsOneToOne, exprsOrd.length, exprsSecond, exprs.length, exprsSecond.length - exprs.length);

                    BoolExpr oneToOne = ctx.mkForall(exprsOneToOne
                            , ctx.mkImplies(ctx.mkAnd(ctx.mkEq(
                                        ordFunc.apply(exprsFirst)
                                        , ordFunc.apply(exprsSecond)))
                                    , ctx.mkAnd(ands))
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

                    goal.add(eqZero);
                    goal.add(ordExpr);
                    goal.add(invExpr);
                    goal.add(oneToOne);

                    cardinalityFuncMap.put(exprToIntCast.toString(), cardFunc);
                    //orderFuncMap.put(exprToIntCast.toString(), ordFunc);
                    return (BitVecExpr) cardFunc.apply(exprs);
                case SUM:
                    Variable v = Variable.unary("x!" + depth);
                    SumExpression sumExpression = (SumExpression) v.count().sum(v.oneOf(exprToIntCast.expression()));

                    variables = new HashSet<>();
                    abstractVoidVisitor = new AbstractVoidVisitor() {
                        private Set<Node> visitedNodes = new HashSet<>();

                        @Override
                        protected boolean visited(Node n) {
                            if (visitedNodes.contains(n))
                                return true;
                            visitedNodes.add(n);
                            return false;
                        }

                        @Override
                        public void visit(Variable variable) {
                            variables.add(variable);
                            super.visit(variable);
                        }
                    };

                    count++;

                    abstractVoidVisitor.visit(sumExpression);
                    usedExprs = variables.stream()
                            .filter(e -> variableExprMap.containsKey(e))
                            .map(variableExprMap::get)
                            .collect(Collectors.toSet());

                    exprs = usedExprs.toArray(new Expr[usedExprs.size()]);

                    Sort[] sumSorts = new Sort[exprs.length];
                    Arrays.fill(sumSorts, UNIV);
                    FuncDecl sum = ctx.mkFuncDecl("SUM[" + sumExpression.toString() + "]" + count, sumSorts, ctx.mkBitVecSort(BIT_SIZE));

                    sorts = new Sort[exprs.length];
                    Arrays.fill(sorts, UNIV);
                    cardFunc = ctx.mkFuncDecl("#[" + exprToIntCast.expression().toString() + "]" + count, sorts, ctx.mkBitVecSort(BIT_SIZE));

                    ordSorts = new Sort[1 + exprs.length];
                    Arrays.fill(ordSorts, UNIV);
                    ordFunc = ctx.mkFuncDecl("ord[" + exprToIntCast.expression().toString() + "]" + count, ordSorts, ctx.mkBitVecSort(BIT_SIZE));

                    Expr[] ordExprs = new Expr[1];
                    BoolExpr[] declTypeRules = new BoolExpr[1];

                    ordExprs[0] = ctx.mkConst(v.name(), UNIV);
                    declTypeRules[0] = visit(exprToIntCast.expression(), depth + 1, new Expr[] {ordExprs[0]});
                    variableExprMap.put(v, ordExprs[0]);

                    Expr exprV = ordExprs[0];

                    Expr[] exprsPlusOrd = new Expr[exprs.length + ordExprs.length];
                    System.arraycopy(exprs, 0, exprsPlusOrd, 0, exprs.length);
                    System.arraycopy(ordExprs, 0, exprsPlusOrd, exprs.length, ordExprs.length);

                    ordExpr = ctx.mkForall(ordExprs,
                            ctx.mkImplies(ctx.mkAnd(declTypeRules),
                                    ctx.mkAnd(
                                            ctx.mkBVSLE(ctx.mkBV(1, BIT_SIZE), (BitVecExpr) ordFunc.apply(exprsPlusOrd))
                                            , ctx.mkBVSLE((BitVecExpr) ordFunc.apply(exprsPlusOrd), (BitVecExpr) cardFunc.apply(exprs))))
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

                    if (exprs.length > 0) {
                        ordExpr = ctx.mkForall(exprs, ordExpr
                                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
                    }

                    BitVecExpr bitVecExpr = ctx.mkBVConst("i!" + (depth + 1), BIT_SIZE);
                    invExpr = ctx.mkForall(new Expr[] {bitVecExpr},
                            ctx.mkImplies(ctx.mkAnd(
                                    ctx.mkBVSLE(ctx.mkBV(1, BIT_SIZE), bitVecExpr)
                                    , ctx.mkBVSLE(bitVecExpr, (BitVecExpr) cardFunc.apply(exprs)))
                                    , ctx.mkExists(ordExprs, ctx.mkAnd(
                                            ctx.mkEq(bitVecExpr, ordFunc.apply(exprsPlusOrd))
                                            , ctx.mkAnd(declTypeRules))
                                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null))
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

                    if (exprs.length > 0) {
                        invExpr = ctx.mkForall(exprs, invExpr
                                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
                    }

                    Expr[] oneToOneExprs = new Expr[ordExprs.length * 2];
                    for (int i = 0; i < oneToOneExprs.length; i++) {
                        oneToOneExprs[i] = ctx.mkConst("x!" + (i + depth), UNIV);
                    }

                    BoolExpr[] oneToOneEqs = new BoolExpr[ordExprs.length];
                    for (int i = 0; i < oneToOneEqs.length; i++) {
                        oneToOneEqs[i] = ctx.mkEq(oneToOneExprs[i], oneToOneExprs[ordExprs.length + i]);
                    }

                    Expr[] firstEq = new Expr[exprsPlusOrd.length];
                    System.arraycopy(exprs, 0, firstEq, 0, exprs.length);
                    System.arraycopy(oneToOneExprs, 0, firstEq, exprs.length, ordExprs.length);
                    Expr[] secondEq = new Expr[exprsPlusOrd.length];
                    System.arraycopy(exprs, 0, secondEq, 0, exprs.length);
                    System.arraycopy(oneToOneExprs, ordExprs.length, secondEq, exprs.length, ordExprs.length);

                    BoolExpr oneToOneExpr = ctx.mkForall(oneToOneExprs, ctx.mkImplies(
                            ctx.mkEq(ordFunc.apply(firstEq), ordFunc.apply(secondEq))
                            , ctx.mkAnd(oneToOneEqs))
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

                    if (exprs.length > 0) {
                        oneToOneExpr = ctx.mkForall(exprs, oneToOneExpr
                                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
                    }

                    Sort[] sumFuncSorts = new Sort[exprs.length + 1];
                    Arrays.fill(sumFuncSorts, UNIV);
                    sumFuncSorts[sumFuncSorts.length - 1] = ctx.mkBitVecSort(BIT_SIZE);

                    FuncDecl sumFunc = ctx.mkFuncDecl(sumExpression.toString() + count, sumFuncSorts, ctx.mkBitVecSort(BIT_SIZE));

                    Expr[] sumExprs = new Expr[ordExprs.length + 1];
                    System.arraycopy(ordExprs, 0, sumExprs, 0, ordExprs.length);
                    sumExprs[sumExprs.length - 1] = bitVecExpr;

                    Expr[] exprsPlusBV = new Expr[exprs.length + 1];
                    System.arraycopy(exprs, 0, exprsPlusBV, 0, exprs.length);
                    exprsPlusBV[exprsPlusBV.length - 1] = bitVecExpr;

                    Expr[] exprsPlusBVminus1 = new Expr[exprs.length + 1];
                    System.arraycopy(exprs, 0, exprsPlusBVminus1, 0, exprs.length);
                    exprsPlusBVminus1[exprsPlusBVminus1.length - 1] = ctx.mkBVSub(bitVecExpr, ctx.mkBV(1, BIT_SIZE));

                    Sort[] noToResultSorts = new Sort[exprs.length + 1];
                    Arrays.fill(noToResultSorts, UNIV);
                    noToResultSorts[noToResultSorts.length - 1] = ctx.mkBitVecSort(BIT_SIZE);

                    FuncDecl noToResultFunc = ctx.mkFuncDecl("NumberToResult[" + exprToIntCast.expression().toString() + "]" + count
                        , noToResultSorts, ctx.mkBitVecSort(BIT_SIZE));
                    BoolExpr noToResultExpr = ctx.mkForall(sumExprs, ctx.mkImplies(ctx.mkEq(ordFunc.apply(exprsPlusOrd), bitVecExpr)
                            , ctx.mkEq(noToResultFunc.apply(exprsPlusBV), univToInt == null ? ctx.mkBV(0, BIT_SIZE) : univToInt.apply(exprV)))
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
                    if (exprs.length > 0) {
                        noToResultExpr = ctx.mkForall(exprs, noToResultExpr
                                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
                    }

                    BoolExpr sumExpr = ctx.mkForall(new Expr[] {bitVecExpr}
                            , ctx.mkEq(sumFunc.apply(exprsPlusBV)
                                    , ctx.mkITE(ctx.mkAnd(ctx.mkBVSLE(ctx.mkBV(1, BIT_SIZE), bitVecExpr)
                                            , ctx.mkBVSLE(bitVecExpr, (BitVecExpr) cardFunc.apply(exprs)))
                                            , ctx.mkBVAdd((BitVecExpr) sumFunc.apply(exprsPlusBVminus1), (BitVecExpr) noToResultFunc.apply(exprsPlusBV))
                                            , ctx.mkBV(0, BIT_SIZE)))
                            , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
                    if (exprs.length > 0) {
                        sumExpr = ctx.mkForall(exprs, sumExpr
                                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
                    }

                    Expr[] sumEqExprs = new Expr[sumFuncSorts.length];
                    System.arraycopy(exprs, 0, sumEqExprs, 0, exprs.length);
                    sumEqExprs[sumEqExprs.length - 1] = cardFunc.apply(exprs);

                    BoolExpr sumEq = ctx.mkEq(sumFunc.apply(sumEqExprs), sum.apply(exprs));
                    if (exprs.length > 0) {
                        sumEq = ctx.mkForall(exprs, sumEq
                                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
                    }

                    goal.add(ordExpr);
                    goal.add(invExpr);
                    goal.add(oneToOneExpr);
                    goal.add(noToResultExpr);
                    goal.add(sumExpr);
                    goal.add(sumEq);

                    return (BitVecExpr) sum.apply(exprs);
            }
        }
        else if (node instanceof kodkod.ast.SumExpression) {
            SumExpression sumExpression = (SumExpression) node;
            IntExpression expression = sumExpression.intExpr();

            Set<Variable> variables = new HashSet<>();
            AbstractVoidVisitor abstractVoidVisitor = new AbstractVoidVisitor() {
                private Set<Node> visitedNodes = new HashSet<>();

                @Override
                protected boolean visited(Node n) {
                    if (visitedNodes.contains(n))
                        return true;
                    visitedNodes.add(n);
                    return false;
                }

                @Override
                public void visit(Variable variable) {
                    variables.add(variable);
                    super.visit(variable);
                }
            };

            count++;

            abstractVoidVisitor.visit(sumExpression);
            Set<Expr> usedExprs = variables.stream()
                    .filter(e -> variableExprMap.containsKey(e))
                    .map(variableExprMap::get)
                    .collect(Collectors.toSet());

            exprs = usedExprs.toArray(new Expr[usedExprs.size()]);

            Sort[] sumSorts = new Sort[exprs.length];
            Arrays.fill(sumSorts, UNIV);
            FuncDecl sum = ctx.mkFuncDecl("SUM[" + sumExpression.toString() + "]" + count, sumSorts, ctx.mkBitVecSort(BIT_SIZE));

            Sort[] sorts = new Sort[exprs.length];
            Arrays.fill(sorts, UNIV);
            FuncDecl cardFunc = ctx.mkFuncDecl("#[" + expression.toString() + "]" + count, sorts, ctx.mkBitVecSort(BIT_SIZE));

            //BitVecExpr cardinality = ctx.mkBVConst("card[" + expression.toString() + "]", BIT_SIZE);

            Sort[] ordSorts = new Sort[sumExpression.decls().size() + exprs.length];
            Arrays.fill(ordSorts, UNIV);
            FuncDecl ordFunc = ctx.mkFuncDecl("ord[" + sumExpression.decls().toString() + "]" + count, ordSorts, ctx.mkBitVecSort(BIT_SIZE));

            Expr[] ordExprs = new Expr[sumExpression.decls().size()];
            BoolExpr[] declTypeRules = new BoolExpr[sumExpression.decls().size()];
            for (int i = 0; i < ordExprs.length; i++) {
                ordExprs[i] = ctx.mkConst(sumExpression.decls().get(i).variable().name(), UNIV);
                declTypeRules[i] = visit(sumExpression.decls().get(i).expression(), depth, new Expr[] {ordExprs[i]});
                variableExprMap.put(sumExpression.decls().get(i).variable(), ordExprs[i]);
                //variableDeclMap.put(sumExpression.decls().get(i).variable(), sumExpression.decls().get(i).expression());
                //exprBoolExprMap.put(ordExprs[i], declTypeRules[i]);
            }

            Expr[] exprsPlusOrd = new Expr[exprs.length + ordExprs.length];
            System.arraycopy(exprs, 0, exprsPlusOrd, 0, exprs.length);
            System.arraycopy(ordExprs, 0, exprsPlusOrd, exprs.length, ordExprs.length);

            BoolExpr ordExpr = ctx.mkForall(ordExprs,
                    ctx.mkImplies(ctx.mkAnd(declTypeRules),
                            ctx.mkAnd(
                                    ctx.mkBVSLE(ctx.mkBV(1, BIT_SIZE), (BitVecExpr) ordFunc.apply(exprsPlusOrd))
                                    , ctx.mkBVSLE((BitVecExpr) ordFunc.apply(exprsPlusOrd), (BitVecExpr) cardFunc.apply(exprs))))
                    , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

            if (exprs.length > 0) {
                ordExpr = ctx.mkForall(exprs, ordExpr
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
            }

            BitVecExpr bitVecExpr = ctx.mkBVConst("i!" + (depth + 1), BIT_SIZE);
            BoolExpr invExpr = ctx.mkForall(new Expr[] {bitVecExpr},
                        ctx.mkImplies(ctx.mkAnd(
                                ctx.mkBVSLE(ctx.mkBV(1, BIT_SIZE), bitVecExpr)
                                , ctx.mkBVSLE(bitVecExpr, (BitVecExpr) cardFunc.apply(exprs)))
                            , ctx.mkExists(ordExprs, ctx.mkAnd(
                                                        ctx.mkEq(bitVecExpr, ordFunc.apply(exprsPlusOrd))
                                                        , ctx.mkAnd(declTypeRules))
                                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null))
                    , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

            if (exprs.length > 0) {
                invExpr = ctx.mkForall(exprs, invExpr
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
            }

            Expr[] oneToOneExprs = new Expr[ordExprs.length * 2];
            for (int i = 0; i < oneToOneExprs.length; i++) {
                oneToOneExprs[i] = ctx.mkConst("x!" + (i + depth), UNIV);
            }

            BoolExpr[] oneToOneEqs = new BoolExpr[ordExprs.length];
            for (int i = 0; i < oneToOneEqs.length; i++) {
                oneToOneEqs[i] = ctx.mkEq(oneToOneExprs[i], oneToOneExprs[ordExprs.length + i]);
            }

            Expr[] firstEq = new Expr[exprsPlusOrd.length];
            System.arraycopy(exprs, 0, firstEq, 0, exprs.length);
            System.arraycopy(oneToOneExprs, 0, firstEq, exprs.length, ordExprs.length);
            Expr[] secondEq = new Expr[exprsPlusOrd.length];
            System.arraycopy(exprs, 0, secondEq, 0, exprs.length);
            System.arraycopy(oneToOneExprs, ordExprs.length, secondEq, exprs.length, ordExprs.length);

            BoolExpr oneToOneExpr = ctx.mkForall(oneToOneExprs, ctx.mkImplies(
                                            ctx.mkEq(ordFunc.apply(firstEq), ordFunc.apply(secondEq))
                                            , ctx.mkAnd(oneToOneEqs))
                    , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

            if (exprs.length > 0) {
                oneToOneExpr = ctx.mkForall(exprs, oneToOneExpr
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
            }

            Sort[] sumFuncSorts = new Sort[exprs.length + 1];
            Arrays.fill(sumFuncSorts, UNIV);
            sumFuncSorts[sumFuncSorts.length - 1] = ctx.mkBitVecSort(BIT_SIZE);

            FuncDecl sumFunc = ctx.mkFuncDecl(sumExpression.toString() + count, sumFuncSorts, ctx.mkBitVecSort(BIT_SIZE));

            Expr[] sumExprs = new Expr[ordExprs.length + 1];
            System.arraycopy(ordExprs, 0, sumExprs, 0, ordExprs.length);
            sumExprs[sumExprs.length - 1] = bitVecExpr;

            Expr[] exprsPlusBV = new Expr[exprs.length + 1];
            System.arraycopy(exprs, 0, exprsPlusBV, 0, exprs.length);
            exprsPlusBV[exprsPlusBV.length - 1] = bitVecExpr;

            Expr[] exprsPlusBVminus1 = new Expr[exprs.length + 1];
            System.arraycopy(exprs, 0, exprsPlusBVminus1, 0, exprs.length);
            exprsPlusBVminus1[exprsPlusBVminus1.length - 1] = ctx.mkBVSub(bitVecExpr, ctx.mkBV(1, BIT_SIZE));

            Sort[] noToResultSorts = new Sort[exprs.length + 1];
            Arrays.fill(noToResultSorts, UNIV);
            noToResultSorts[noToResultSorts.length - 1] = ctx.mkBitVecSort(BIT_SIZE);

            FuncDecl noToResultFunc = ctx.mkFuncDecl("NumberToResult[" + expression.toString() + "]" + count, noToResultSorts, ctx.mkBitVecSort(BIT_SIZE));
            BoolExpr noToResultExpr = ctx.mkForall(sumExprs, ctx.mkImplies(ctx.mkEq(ordFunc.apply(exprsPlusOrd), bitVecExpr)
                    , ctx.mkEq(noToResultFunc.apply(exprsPlusBV), visitIntExpression(expression, depth, ordExprs)))
                    , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
            if (exprs.length > 0) {
                noToResultExpr = ctx.mkForall(exprs, noToResultExpr
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
            }

            BoolExpr sumExpr = ctx.mkForall(new Expr[] {bitVecExpr}
                    , ctx.mkEq(sumFunc.apply(exprsPlusBV)
                            , ctx.mkITE(ctx.mkAnd(ctx.mkBVSLE(ctx.mkBV(1, BIT_SIZE), bitVecExpr)
                                                , ctx.mkBVSLE(bitVecExpr, (BitVecExpr) cardFunc.apply(exprs)))
                                        , ctx.mkBVAdd((BitVecExpr) sumFunc.apply(exprsPlusBVminus1), (BitVecExpr) noToResultFunc.apply(exprsPlusBV))
                                        , ctx.mkBV(0, BIT_SIZE)))
                    , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
            if (exprs.length > 0) {
                sumExpr = ctx.mkForall(exprs, sumExpr
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
            }

            Expr[] sumEqExprs = new Expr[sumFuncSorts.length];
            System.arraycopy(exprs, 0, sumEqExprs, 0, exprs.length);
            sumEqExprs[sumEqExprs.length - 1] = cardFunc.apply(exprs);

            BoolExpr sumEq = ctx.mkEq(sumFunc.apply(sumEqExprs), sum.apply(exprs));
            if (exprs.length > 0) {
                sumEq = ctx.mkForall(exprs, sumEq
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
            }

            goal.add(ordExpr);
            goal.add(invExpr);
            goal.add(oneToOneExpr);
            goal.add(noToResultExpr);
            goal.add(sumExpr);
            goal.add(sumEq);

            return (BitVecExpr) sum.apply(exprs);
        }
        else if (node instanceof IfIntExpression) {
            IfIntExpression ifExpression = (IfIntExpression) node;
            return (BitVecExpr) ctx.mkITE(visit(ifExpression.condition(), depth, exprs)
                    , visitIntExpression(ifExpression.thenExpr(), depth, exprs)
                    , visitIntExpression(ifExpression.elseExpr(), depth, exprs));
        }
        else if (node instanceof UnaryIntExpression) {
            UnaryIntExpression unaryIntExpression = (UnaryIntExpression) node;
            BitVecExpr expr = visitIntExpression(unaryIntExpression.intExpr(), depth, exprs);
            switch (unaryIntExpression.op()) {
                case SGN:
                    return (BitVecExpr) ctx.mkITE(ctx.mkEq(expr, ctx.mkBV(0, BIT_SIZE))
                            , ctx.mkBV(0, BIT_SIZE)
                            , ctx.mkITE(ctx.mkBVSGT(expr, ctx.mkBV(0, BIT_SIZE))
                                    , ctx.mkBV(1, BIT_SIZE)
                                    , ctx.mkBV(-1, BIT_SIZE)));
                case NOT:
                    return ctx.mkBVNot(expr);
                case NEG:
                    return ctx.mkBVNeg(expr);
                case ABS:
                    return (BitVecExpr) ctx.mkITE(ctx.mkBVSLT(expr, ctx.mkBV(0, BIT_SIZE)), ctx.mkBVNeg(expr), expr);
            }
        }
        else if (node instanceof BinaryIntExpression) {
            BinaryIntExpression binaryIntExpression = (BinaryIntExpression) node;
            BitVecExpr left = visitIntExpression(binaryIntExpression.left(), depth, exprs);
            BitVecExpr right = visitIntExpression(binaryIntExpression.right(), depth, exprs);
            switch (binaryIntExpression.op()) {
                case AND:
                    return ctx.mkBVAND(left, right);
                case OR:
                    return ctx.mkBVOR(left, right);
                case SHA:
                    return ctx.mkBVASHR(left, right);
                case SHL:
                    return ctx.mkBVSHL(left, right);
                case SHR:
                    return ctx.mkBVLSHR(left, right);
                case XOR:
                    return ctx.mkBVXOR(left, right);
                case PLUS:
                    return ctx.mkBVAdd(left, right);
                case MINUS:
                    return ctx.mkBVSub(left, right);
                case DIVIDE:
                    return ctx.mkBVSDiv(left, right);
                case MODULO:
                    return ctx.mkBVSMod(left, right);
                case MULTIPLY:
                    return ctx.mkBVMul(left, right);
            }
        }
        else if (node instanceof kodkod.ast.NaryIntExpression) {
            NaryIntExpression naryIntExpression = (NaryIntExpression) node;
            Iterator<IntExpression> iterator = naryIntExpression.iterator();
            if (iterator.hasNext()) {
                BitVecExpr expr = visitIntExpression(iterator.next(), depth, exprs);
                switch (naryIntExpression.op()) {
                    case MULTIPLY:
                        while (iterator.hasNext()) {
                            expr = ctx.mkBVMul(expr, visitIntExpression(iterator.next(), depth, exprs));
                        }
                        return expr;
                    case PLUS:
                        while (iterator.hasNext()) {
                            expr = ctx.mkBVAdd(expr, visitIntExpression(iterator.next(), depth, exprs));
                        }
                        return expr;
                    case AND:
                        while (iterator.hasNext()) {
                            expr = ctx.mkBVAND(expr, visitIntExpression(iterator.next(), depth, exprs));
                        }
                        return expr;
                    case OR:
                        while (iterator.hasNext()) {
                            expr = ctx.mkBVOR(expr, visitIntExpression(iterator.next(), depth, exprs));
                        }
                        return expr;
                }
            }
        }
        return ctx.mkBV(0, BIT_SIZE);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("Formulas:").append(System.lineSeparator()).append(System.lineSeparator());
        Arrays.stream(goal.getFormulas()).forEach(boolExpr -> {
            sb.append(boolExpr).append(System.lineSeparator());
        });
        sb.append(System.lineSeparator()).append(System.lineSeparator());
        sb.append("All input:").append(System.lineSeparator()).append(System.lineSeparator());
        sb.append(solver);
        return sb.toString();
    }

    @Override
    public int numberOfVariables() {
        return 0;
    }

    @Override
    public int numberOfClauses() {
        return 0;
    }

    @Override
    public void addVariables(int numVars) {

    }

    @Override
    public boolean addClause(int[] lits) {
        return false;
    }

    @Override
    public boolean solve() throws SATAbortedException {
        return false;
    }

    @Override
    public boolean valueOf(int variable) {
        return false;
    }

    @Override
    public void free() {

    }
}
