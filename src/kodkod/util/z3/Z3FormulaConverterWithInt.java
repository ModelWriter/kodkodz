package kodkod.util.z3;

import com.microsoft.z3.*;
import kodkod.ast.*;
import kodkod.ast.operator.ExprOperator;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.instance.Bounds;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Created by harun on 7/16/18.
 */
public class Z3FormulaConverterWithInt implements ReturnVisitor<BoolExpr, BoolExpr, BoolExpr, IntExpr> {

    private static final String quantifierPrefix = "q!";
    private static final String skolemPrefix = "s!";
    
    private int quantifierID;
    private int skolemID;
    private int BIT_SIZE;

    private Context ctx;
    private Map<Expression, FuncDecl> funcDeclMap;
    private Sort UNIV;
    private FuncDecl univToInt;

    private Map<String, FuncDecl> intExprFuncMap;

    private Map<Variable, Expr> variableExprMap;
    private Expr[] exprs;
    private int varCount;

    private Set<BoolExpr> goal;

    int constSize;

    public Z3FormulaConverterWithInt(Context ctx, Sort UNIV, Map<Expression, FuncDecl> funcDeclMap
            , Map<Object, Expr> objectExprMap, int BIT_SIZE) {
        this.ctx = ctx;
        this.funcDeclMap = funcDeclMap;
        this.UNIV = UNIV;
        this.BIT_SIZE = BIT_SIZE;

        this.variableExprMap = new HashMap<>();
        this.exprs = null;
        this.varCount = 0;
        this.quantifierID = 0;
        this.skolemID = 0;

        intExprFuncMap = new HashMap<>();

        constSize = objectExprMap.keySet().size();

        this.goal = new HashSet<>();

        if (objectExprMap.entrySet().stream().anyMatch(e -> e.getKey() instanceof Integer)) {
            FuncDecl intsFuncDecl = ctx.mkFuncDecl("Ints", new Sort[]{UNIV}, ctx.mkBoolSort());
            funcDeclMap.put(Relation.INTS, intsFuncDecl);

            univToInt = ctx.mkFuncDecl("toInt", UNIV, ctx.mkIntSort());

            objectExprMap.forEach(((o, expr) -> {
                if (o instanceof Integer) {
                    goal.add((BoolExpr) ctx.mkApp(intsFuncDecl, expr));
                    goal.add(ctx.mkEq(ctx.mkApp(univToInt, expr), ctx.mkInt((Integer) o)));
                } else {
                    goal.add(ctx.mkNot((BoolExpr) ctx.mkApp(intsFuncDecl, expr)));
                    goal.add(ctx.mkEq(ctx.mkApp(univToInt, expr), ctx.mkInt(0)));
                }
            }));
        }
    }

    public BoolExpr convert(Formula formula) {
        this.exprs = new Expr[0];
        this.varCount = 0;
        this.variableExprMap.clear();
        return formula.accept(this);
    }

    public Set<BoolExpr> getCreatedBoolExpressions() {
        return goal;
    }

    @Override
    public BoolExpr visit(Decls decls) {
        BoolExpr[] boolExprs = new BoolExpr[decls.size()];
        for (int i = 0; i < decls.size(); i++) {
            boolExprs[i] = decls.get(i).accept(this);
        }
        return ctx.mkAnd(boolExprs);
    }

    @Override
    public BoolExpr visit(Decl decl) {
        return decl.variable().in(decl.expression()).accept(this);
    }

    @Override
    public BoolExpr visit(Relation relation) {
        return (BoolExpr) ctx.mkApp(funcDeclMap.get(relation), exprs);
    }

    @Override
    public BoolExpr visit(Variable variable) {
        return ctx.mkEq(variableExprMap.get(variable), exprs[0]);
    }

    @Override
    public BoolExpr visit(ConstantExpression constExpr) {
        if (constExpr == Relation.IDEN) {
            return exprs.length == 2 ? ctx.mkEq(exprs[0], exprs[1]) : ctx.mkFalse();
        }
        if (constExpr == Relation.NONE) {
            return exprs.length == 0 ? ctx.mkTrue() : ctx.mkFalse();
        }
        if (constExpr == Relation.UNIV) {
            return exprs.length == 1 ? ctx.mkTrue() : ctx.mkFalse();
        }

        FuncDecl funcDecl = funcDeclMap.get(constExpr);
        return funcDecl == null ? ctx.mkFalse() : (BoolExpr) ctx.mkApp(funcDecl, exprs);
    }

    @Override
    public BoolExpr visit(UnaryExpression unaryExpr) {
        switch (unaryExpr.op()) {
            case TRANSPOSE:
                Expr[] temp = exprs;
                exprs = new Expr[] {exprs[1], exprs[0]};
                BoolExpr boolExpr = unaryExpr.expression().accept(this);
                exprs = temp;
                return boolExpr;
            case REFLEXIVE_CLOSURE:
                int loopCount = constSize - 1;

                Expression unionExpr = Relation.IDEN;
                for (int i = 0; i < loopCount; i++) {
                    unionExpr = Relation.IDEN.union(unaryExpr.expression().join(unionExpr));
                }

                return unionExpr.accept(this);
            case CLOSURE:
                loopCount = constSize - 1;

                unionExpr = Relation.IDEN;
                for (int i = 0; i < loopCount; i++) {
                    unionExpr = Relation.IDEN.union(unaryExpr.expression().join(unionExpr));
                }

                if (unionExpr instanceof BinaryExpression && ((BinaryExpression) unionExpr).op().equals(ExprOperator.UNION))
                    return ((BinaryExpression) unionExpr).right().accept(this);
                else {
                    return ctx.mkFalse();
                }
            default:
                return ctx.mkFalse();
        }
    }

    @Override
    public BoolExpr visit(BinaryExpression binExpr) {
        switch (binExpr.op()) {
            case JOIN:
                Expr expr = ctx.mkConst("x!" + varCount++, UNIV);

                Expression leftExpression = binExpr.left();
                Expression rightExpression = binExpr.right();

                Expr[] leftExprs = new Expr[leftExpression.arity()];

                System.arraycopy(exprs, 0, leftExprs, 0, leftExprs.length - 1);
                leftExprs[leftExprs.length - 1] = expr;

                Expr[] rightExprs = new Expr[rightExpression.arity()];

                rightExprs[0] = expr;
                System.arraycopy(exprs, exprs.length - rightExprs.length + 1, rightExprs, 1, rightExprs.length - 1);

                if (leftExpression instanceof Variable) {
                    rightExprs[0] = variableExprMap.get(leftExpression);

                    Expr[] temp = exprs;
                    exprs = rightExprs;
                    BoolExpr boolExpr = rightExpression.accept(this);
                    exprs = temp;
                    return boolExpr;
                }
                else if (rightExpression instanceof Variable) {
                    leftExprs[leftExprs.length - 1] = variableExprMap.get(rightExpression);
                    Expr[] temp = exprs;
                    exprs = leftExprs;
                    BoolExpr boolExpr = leftExpression.accept(this);
                    exprs = temp;
                    return boolExpr;
                }

                Expr[] temp = exprs;

                exprs = leftExprs;
                BoolExpr leftBoolExpr = leftExpression.accept(this);
                exprs = rightExprs;
                BoolExpr rightBoolExpr = rightExpression.accept(this);

                exprs = temp;

                return ctx.mkExists(new Expr[] {expr}
                        , ctx.mkAnd(leftBoolExpr, rightBoolExpr)
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), ctx.mkSymbol(skolemPrefix + skolemID++));
            case UNION:
                return ctx.mkOr(binExpr.left().accept(this), binExpr.right().accept(this));
            case INTERSECTION:
                return ctx.mkAnd(binExpr.left().accept(this), binExpr.right().accept(this));
            case PRODUCT:
                leftExpression = binExpr.left();
                rightExpression = binExpr.right();

                leftExprs = new Expr[leftExpression.arity()];
                System.arraycopy(exprs, 0, leftExprs, 0, leftExprs.length);

                rightExprs = new Expr[rightExpression.arity()];
                System.arraycopy(exprs, leftExpression.arity(), rightExprs, 0, rightExprs.length);

                temp = exprs;

                exprs = leftExprs;
                leftBoolExpr = leftExpression.accept(this);
                exprs = rightExprs;
                rightBoolExpr = rightExpression.accept(this);

                exprs = temp;

                return ctx.mkAnd(leftBoolExpr, rightBoolExpr);
            case DIFFERENCE:
                return ctx.mkAnd(binExpr.left().accept(this), ctx.mkNot(binExpr.right().accept(this)));
            case OVERRIDE:
                BoolExpr boolExpr = binExpr.right().accept(this);
                return (BoolExpr) ctx.mkITE(boolExpr, ctx.mkTrue(), binExpr.left().accept(this));
            default:
                return ctx.mkFalse();
        }
    }

    @Override
    public BoolExpr visit(NaryExpression expr) {
        switch (expr.op()) {
            case UNION:
                BoolExpr[] boolExprs = new BoolExpr[expr.size()];
                for (int i = 0; i < boolExprs.length; i++) {
                    boolExprs[i] = expr.child(i).accept(this);
                }
                return ctx.mkOr(boolExprs);
            case PRODUCT:
                boolExprs = new BoolExpr[expr.size()];
                for (int i = 0; i < boolExprs.length; i++) {
                    int start = 0;

                    for (int j = 0; j < i; j++)
                        start += expr.child(i - 1).arity();

                    Expression expression = expr.child(i);
                    Expr[] exprs1 = new Expr[expression.arity()];

                    System.arraycopy(exprs, start, exprs1, 0, exprs1.length);

                    Expr[] temp = exprs;

                    exprs = exprs1;
                    boolExprs[i] = expression.accept(this);

                    exprs = temp;
                }
                return ctx.mkAnd(boolExprs);
            case INTERSECTION:
                boolExprs = new BoolExpr[expr.size()];
                for (int i = 0; i < boolExprs.length; i++) {
                    boolExprs[i] = expr.child(i).accept(this);
                }
                return ctx.mkAnd(boolExprs);
            case OVERRIDE:
                if (expr.size() <= 0)
                    return ctx.mkFalse();

                BoolExpr boolExpr = expr.child(0).accept(this);
                for (int i = 1; i < expr.size(); i++) {
                    BoolExpr temp = expr.child(i).accept(this);
                    boolExpr = (BoolExpr) ctx.mkITE(temp, ctx.mkTrue(), boolExpr);
                }

                return boolExpr;
            default:
                return ctx.mkFalse();
        }
    }

    @Override
    public BoolExpr visit(Comprehension comprehension) {
        // TODO: Implement this.
        return ctx.mkFalse();
    }

    @Override
    public BoolExpr visit(IfExpression ifExpr) {
        return (BoolExpr) ctx.mkITE(ifExpr.condition().accept(this)
                , ifExpr.thenExpr().accept(this)
                , ifExpr.elseExpr().accept(this));
    }

    @Override
    public BoolExpr visit(ProjectExpression project) {
        // TODO: Implement this.
        return ctx.mkFalse();
    }

    @Override
    public BoolExpr visit(IntToExprCast castExpr) {
        // TODO: Implement this.
        return ctx.mkFalse();
    }

    @Override
    public IntExpr visit(IntConstant intConst) {
        return ctx.mkInt(intConst.value());
    }

    @Override
    public IntExpr visit(IfIntExpression intExpr) {
        return (IntExpr) ctx.mkITE(intExpr.condition().accept(this)
                , intExpr.thenExpr().accept(this)
                , intExpr.elseExpr().accept(this));
    }

    public FuncDecl cardinality(Expression expression) {
        VariableDetector variableDetector = new VariableDetector();
        expression.accept(variableDetector);

        Set<Variable> variables = variableDetector.variables().stream()
                .filter(v -> variableExprMap.containsKey(v))
                .collect(Collectors.toSet());

        Map<Variable, Expr> tempMap = new HashMap<>();

        variables.forEach(variable -> {
            Expr expr = variableExprMap.get(variable);
            if (expr.isConst()) {
                tempMap.put(variable, expr);
                variableExprMap.put(variable, ctx.mkConst("x!" + varCount++, UNIV));
            }
        });

        Expr[] inExprs = variables.stream().sorted(Comparator.comparingInt(Object::hashCode)).map(v -> variableExprMap.get(v)).toArray(Expr[]::new);

        int inSize = variables.size();
        int outSize = expression.arity();

        Sort[] inSorts = new Sort[inSize];
        Arrays.fill(inSorts, UNIV);

        FuncDecl cardinalityFunc = ctx.mkFuncDecl("#[" + expression.toString() + "]" + varCount++
                , inSorts, ctx.mkIntSort());

        Sort[] ordSorts = new Sort[inSize + outSize];
        Arrays.fill(ordSorts, UNIV);

        FuncDecl ordFunc = ctx.mkFuncDecl("ord[" + expression.toString() + "]" + varCount++, ordSorts, ctx.mkIntSort());

        Expr[] ordExprs = new Expr[ordSorts.length];
        System.arraycopy(inExprs, 0, ordExprs, 0, inSize);
        for (int i = inSize; i < ordExprs.length; i++) {
            ordExprs[i] = ctx.mkConst("x!" + varCount++, UNIV);
        }

        Expr[] outExprs = new Expr[outSize];
        System.arraycopy(ordExprs, inSize, outExprs, 0, outSize);

        IntExpr intExpr = ctx.mkIntConst("i!" + varCount++);

        Expr[] invExprs = new Expr[inSize + 1];
        System.arraycopy(inExprs, 0, invExprs, 0, inSize);
        invExprs[invExprs.length - 1] = intExpr;

        Expr[] temp;

        // crd = 0 ⇔ ∀f : FSO, ¬isFSO(f )
        // ****************************************** //
        BoolExpr boolExprEqZero = ctx.mkIff(ctx.mkEq(cardinalityFunc.apply(inExprs), ctx.mkInt(0)), expression.no().accept(this));

        if (inSize > 0) {
            boolExprEqZero = ctx.mkForall(inExprs, boolExprEqZero
                    , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
        }
        // ****************************************** //

        // ∀f : FSO | isFSO(f) ⇒ 1 ≤ ord(f ) ≤ crd
        // ****************************************** //

        temp = exprs;
        exprs = outExprs;

        BoolExpr boolExprOrd = ctx.mkForall(ordExprs
                , ctx.mkImplies(expression.accept(this)
                        , ctx.mkAnd(ctx.mkLe(ctx.mkInt(1), (IntExpr) ordFunc.apply(ordExprs))
                                , ctx.mkLe((IntExpr) ordFunc.apply(ordExprs)
                                        , (IntExpr) cardinalityFunc.apply(inExprs))))
                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

        exprs = temp;

        // ****************************************** //

        // ∀i : Nat | 1 ≤ i ≤ crd ⇒ isFSO(inv(i))
        // inv = ord^−1
        // ****************************************** //

        temp = exprs;
        exprs = outExprs;

        BoolExpr boolExprInv = ctx.mkForall(invExprs,
                ctx.mkImplies(ctx.mkAnd(ctx.mkLe(ctx.mkInt(1), intExpr)
                        , ctx.mkLe(intExpr, (IntExpr) cardinalityFunc.apply(inExprs)))
                        , ctx.mkExists(outExprs, ctx.mkAnd(
                                ctx.mkEq(ordFunc.apply(ordExprs), intExpr)
                                , expression.accept(this))
                                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null))
                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

        exprs = temp;

        Expr[] oneToOneExprs = new Expr[inSize + outSize * 2];
        for (int i = 0; i < oneToOneExprs.length; i++) {
            oneToOneExprs[i] = ctx.mkConst("x!" + varCount++, UNIV);
        }

        Expr[] firstOne = new Expr[ordExprs.length];
        System.arraycopy(oneToOneExprs, 0, firstOne, 0, firstOne.length);

        Expr[] secondOne = new Expr[ordExprs.length];
        System.arraycopy(oneToOneExprs, 0, secondOne, 0, inSize);
        System.arraycopy(oneToOneExprs, ordExprs.length, secondOne, inSize, outSize);

        BoolExpr[] eqs = new BoolExpr[outSize];
        for (int i = 0; i < outSize; i++) {
            eqs[i] = ctx.mkEq(firstOne[i + inSize], secondOne[i + inSize]);
        }

        BoolExpr boolExprOneToOne = ctx.mkForall(oneToOneExprs
                , ctx.mkImplies(ctx.mkEq(ordFunc.apply(firstOne), ordFunc.apply(secondOne))
                        , ctx.mkAnd(eqs))
                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

        // ****************************************** //

        goal.add(boolExprEqZero);
        goal.add(boolExprOrd);
        goal.add(boolExprInv);
        goal.add(boolExprOneToOne);

        variableExprMap.putAll(tempMap);

        return cardinalityFunc;
    }

    public FuncDecl sum(Expression expression) {
        VariableDetector variableDetector = new VariableDetector();
        expression.accept(variableDetector);

        Set<Variable> variables = variableDetector.variables().stream()
                .filter(v -> variableExprMap.containsKey(v))
                .collect(Collectors.toSet());

        Map<Variable, Expr> tempMap = new HashMap<>();

        variables.forEach(variable -> {
            Expr expr = variableExprMap.get(variable);
            if (expr.isConst()) {
                tempMap.put(variable, expr);
                variableExprMap.put(variable, ctx.mkConst("x!" + varCount++, UNIV));
            }
        });

        Expr[] inExprs = variables.stream().sorted(Comparator.comparingInt(Object::hashCode)).map(v -> variableExprMap.get(v)).toArray(Expr[]::new);

        int inSize = variables.size();
        int outSize = expression.arity();

        Sort[] inSorts = new Sort[inSize];
        Arrays.fill(inSorts, UNIV);

        FuncDecl sum = ctx.mkFuncDecl("SUM[" + expression.toString() + "]" + varCount++
                , inSorts, ctx.mkIntSort());

        FuncDecl cardinalityFunc = ctx.mkFuncDecl("#[" + expression.toString() + "]" + varCount++
                , inSorts, ctx.mkIntSort());

        Sort[] sumSorts = new Sort[inSize + 1];
        Arrays.fill(sumSorts, UNIV);
        sumSorts[sumSorts.length - 1] = ctx.mkIntSort();

        FuncDecl sumFunc = ctx.mkFuncDecl("SUM_RECURSIVE[" + expression.toString() + "]" + varCount++
                , sumSorts, ctx.mkIntSort());

        Sort[] ordSorts = new Sort[inSize + outSize];
        Arrays.fill(ordSorts, UNIV);

        FuncDecl ordFunc = ctx.mkFuncDecl("ord[" + expression.toString() + "]" + varCount++, ordSorts, ctx.mkIntSort());

        Expr[] ordExprs = new Expr[ordSorts.length];
        System.arraycopy(inExprs, 0, ordExprs, 0, inSize);
        for (int i = inSize; i < ordExprs.length; i++) {
            ordExprs[i] = ctx.mkConst("x!" + varCount++, UNIV);
        }

        Expr[] outExprs = new Expr[outSize];
        System.arraycopy(ordExprs, inSize, outExprs, 0, outSize);

        IntExpr intExpr = ctx.mkIntConst("i!" + varCount++);

        Sort[] invSorts = new Sort[inSize + 1];
        System.arraycopy(inSorts, 0, invSorts, 0, inSize);
        invSorts[invSorts.length - 1] = ctx.mkIntSort();

        Expr[] invExprs = new Expr[inSize + 1];
        System.arraycopy(inExprs, 0, invExprs, 0, inSize);
        invExprs[invExprs.length - 1] = intExpr;

        Expr[] temp;

        // crd = 0 ⇔ ∀f : FSO, ¬isFSO(f )
        // ****************************************** //
        BoolExpr boolExprEqZero = ctx.mkIff(ctx.mkEq(cardinalityFunc.apply(inExprs), ctx.mkInt(0)), expression.no().accept(this));

        if (inSize > 0) {
            boolExprEqZero = ctx.mkForall(inExprs, boolExprEqZero
                    , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
        }
        // ****************************************** //

        // ∀f : FSO | isFSO(f) ⇒ 1 ≤ ord(f ) ≤ crd
        // ****************************************** //

        temp = exprs;
        exprs = outExprs;

        BoolExpr boolExprOrd = ctx.mkForall(ordExprs
                , ctx.mkImplies(expression.accept(this)
                        , ctx.mkAnd(ctx.mkLe(ctx.mkInt(1), (IntExpr) ordFunc.apply(ordExprs))
                                , ctx.mkLe((IntExpr) ordFunc.apply(ordExprs)
                                        , (IntExpr) cardinalityFunc.apply(inExprs))))
                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

        exprs = temp;

        // ****************************************** //

        // ∀i : Nat | 1 ≤ i ≤ crd ⇒ isFSO(inv(i))
        // inv = ord^−1
        // ****************************************** //

        temp = exprs;
        exprs = outExprs;

        BoolExpr boolExprInv = ctx.mkForall(invExprs,
                ctx.mkImplies(ctx.mkAnd(ctx.mkLe(ctx.mkInt(1), intExpr)
                        , ctx.mkLe(intExpr, (IntExpr) cardinalityFunc.apply(inExprs)))
                        , ctx.mkExists(outExprs, ctx.mkAnd(
                                ctx.mkEq(ordFunc.apply(ordExprs), intExpr)
                                , expression.accept(this))
                                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null))
                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

        exprs = temp;

        Expr[] oneToOneExprs = new Expr[inSize + outSize * 2];
        for (int i = 0; i < oneToOneExprs.length; i++) {
            oneToOneExprs[i] = ctx.mkConst("x!" + varCount++, UNIV);
        }

        Expr[] firstOne = new Expr[ordExprs.length];
        System.arraycopy(oneToOneExprs, 0, firstOne, 0, firstOne.length);

        Expr[] secondOne = new Expr[ordExprs.length];
        System.arraycopy(oneToOneExprs, 0, secondOne, 0, inSize);
        System.arraycopy(oneToOneExprs, ordExprs.length, secondOne, inSize, outSize);

        BoolExpr[] eqs = new BoolExpr[outSize];
        for (int i = 0; i < outSize; i++) {
            eqs[i] = ctx.mkEq(firstOne[i + inSize], secondOne[i + inSize]);
        }

        BoolExpr boolExprOneToOne = ctx.mkForall(oneToOneExprs
                , ctx.mkImplies(ctx.mkEq(ordFunc.apply(firstOne), ordFunc.apply(secondOne))
                        , ctx.mkAnd(eqs))
                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

        // ****************************************** //

        FuncDecl noToResultFunc = ctx.mkFuncDecl("NO[" + expression.toString() + "]" + varCount++
                , invSorts, ctx.mkIntSort());

        Expr[] sumExprs = new Expr[ordExprs.length + 1];
        System.arraycopy(ordExprs, 0, sumExprs, 0, ordExprs.length);
        sumExprs[sumExprs.length - 1] = intExpr;

        BoolExpr boolExprNoToResult = ctx.mkForall(sumExprs, ctx.mkImplies(ctx.mkEq(ordFunc.apply(ordExprs), intExpr)
                , ctx.mkEq(noToResultFunc.apply(invExprs), univToInt == null ? ctx.mkInt(0) : univToInt.apply(outExprs)))
                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

        Expr[] exprsPlusBVminus1 = new Expr[invExprs.length];
        System.arraycopy(inExprs, 0, exprsPlusBVminus1, 0, inSize);
        exprsPlusBVminus1[exprsPlusBVminus1.length - 1] = ctx.mkAdd(intExpr, ctx.mkInt(1));

        BoolExpr boolExprSum = ctx.mkForall(invExprs
                , ctx.mkEq(sumFunc.apply(invExprs)
                        , ctx.mkITE(ctx.mkAnd(ctx.mkLe(ctx.mkInt(1), intExpr)
                                , ctx.mkLe(intExpr, (IntExpr) cardinalityFunc.apply(inExprs)))
                                , ctx.mkAdd((IntExpr) sumFunc.apply(exprsPlusBVminus1), (IntExpr) noToResultFunc.apply(invExprs))
                                , ctx.mkInt(0)))
                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

        Expr[] sumWithCardExprs = new Expr[invSorts.length];
        System.arraycopy(inExprs, 0, sumWithCardExprs, 0, inExprs.length);
        sumWithCardExprs[sumWithCardExprs.length - 1] = ctx.mkInt(1);

        BoolExpr boolExprSumEq = ctx.mkEq(sum.apply(inExprs), sumFunc.apply(sumWithCardExprs));
        if (inSize > 0) {
            boolExprSumEq = ctx.mkForall(inExprs, boolExprSumEq
                    , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
        }

        goal.add(boolExprEqZero);
        goal.add(boolExprOrd);
        goal.add(boolExprInv);
        goal.add(boolExprOneToOne);
        goal.add(boolExprNoToResult);
        goal.add(boolExprSum);
        goal.add(boolExprSumEq);

        variableExprMap.putAll(tempMap);

        intExprFuncMap.put(expression.count().toString(), cardinalityFunc);

        return sum;
    }

    @Override
    public IntExpr visit(ExprToIntCast exprToIntCast) {
        switch (exprToIntCast.op()) {
            case CARDINALITY:
                Expression expression = exprToIntCast.expression();

                if (expression instanceof Variable)
                    return ctx.mkInt(1);

                FuncDecl func = intExprFuncMap.computeIfAbsent(exprToIntCast.toString(), e -> cardinality(expression));

                VariableDetector variableDetector = new VariableDetector();
                expression.accept(variableDetector);
                Expr[] usedExprs = variableDetector.variables().stream().sorted(Comparator.comparingInt(Object::hashCode))
                        .map(v -> variableExprMap.get(v)).filter(Objects::nonNull).toArray(Expr[]::new);

                return (IntExpr) func.apply(usedExprs);
            case SUM:
                expression = exprToIntCast.expression();

                if (univToInt == null)
                    return ctx.mkInt(0);

                if (expression instanceof Variable)
                    return (IntExpr) univToInt.apply(variableExprMap.get(expression));

                func = intExprFuncMap.computeIfAbsent(exprToIntCast.toString(), e -> sum(expression));

                variableDetector = new VariableDetector();
                expression.accept(variableDetector);
                usedExprs = variableDetector.variables().stream().sorted(Comparator.comparingInt(Object::hashCode))
                        .map(v -> variableExprMap.get(v)).filter(Objects::nonNull).toArray(Expr[]::new);

                return (IntExpr) func.apply(usedExprs);
            default:
                return ctx.mkInt(0);
        }
    }

    @Override
    public IntExpr visit(NaryIntExpression naryIntExpression) {
        Iterator<IntExpression> iterator = naryIntExpression.iterator();
        if (iterator.hasNext()) {
            IntExpr expr = iterator.next().accept(this);
            switch (naryIntExpression.op()) {
                case MULTIPLY:
                    while (iterator.hasNext()) {
                        expr = (IntExpr) ctx.mkMul(expr, iterator.next().accept(this));
                    }
                    return expr;
                case PLUS:
                    while (iterator.hasNext()) {
                        expr = (IntExpr) ctx.mkAdd(expr, iterator.next().accept(this));
                    }
                    return expr;
                case AND:
                    while (iterator.hasNext()) {
                        expr = ctx.mkBV2Int(ctx.mkBVAND(ctx.mkInt2BV(BIT_SIZE, expr), ctx.mkInt2BV(BIT_SIZE, iterator.next().accept(this))), true);
                    }
                    return expr;
                case OR:
                    while (iterator.hasNext()) {
                        expr = ctx.mkBV2Int(ctx.mkBVOR(ctx.mkInt2BV(BIT_SIZE, expr), ctx.mkInt2BV(BIT_SIZE, iterator.next().accept(this))), true);
                    }
                    return expr;
            }
        }
        return ctx.mkInt(0);
    }

    @Override
    public IntExpr visit(BinaryIntExpression binaryIntExpression) {
        IntExpr left = binaryIntExpression.left().accept(this);
        IntExpr right = binaryIntExpression.right().accept(this);
        switch (binaryIntExpression.op()) {
            case AND:
                return ctx.mkBV2Int(ctx.mkBVAND(ctx.mkInt2BV(BIT_SIZE, left), ctx.mkInt2BV(BIT_SIZE, right)), true);
            case OR:
                return ctx.mkBV2Int(ctx.mkBVOR(ctx.mkInt2BV(BIT_SIZE, left), ctx.mkInt2BV(BIT_SIZE, right)), true);
            case SHA:
                return ctx.mkBV2Int(ctx.mkBVASHR(ctx.mkInt2BV(BIT_SIZE, left), ctx.mkInt2BV(BIT_SIZE, right)), true);
            case SHL:
                return ctx.mkBV2Int(ctx.mkBVSHL(ctx.mkInt2BV(BIT_SIZE, left), ctx.mkInt2BV(BIT_SIZE, right)), true);
            case SHR:
                return ctx.mkBV2Int(ctx.mkBVLSHR(ctx.mkInt2BV(BIT_SIZE, left), ctx.mkInt2BV(BIT_SIZE, right)), true);
            case XOR:
                return ctx.mkBV2Int(ctx.mkBVXOR(ctx.mkInt2BV(BIT_SIZE, left), ctx.mkInt2BV(BIT_SIZE, right)), true);
            case PLUS:
                return (IntExpr) ctx.mkAdd(left, right);
            case MINUS:
                return (IntExpr) ctx.mkSub(left, right);
            case DIVIDE:
                return (IntExpr) ctx.mkDiv(left, right);
            case MODULO:
                return ctx.mkMod(left, right);
            case MULTIPLY:
                return (IntExpr) ctx.mkMul(left, right);
            default:
                return ctx.mkInt(0);
        }
    }

    @Override
    public IntExpr visit(UnaryIntExpression intExpr) {
        IntExpr expr = intExpr.intExpr().accept(this);
        switch (intExpr.op()) {
            case SGN:
                return (IntExpr) ctx.mkITE(ctx.mkEq(expr, ctx.mkInt(0))
                        , ctx.mkInt(0)
                        , ctx.mkITE(ctx.mkGt(expr, ctx.mkInt(0))
                                , ctx.mkInt(1)
                                , ctx.mkInt(-1)));
            case NOT:
                return ctx.mkBV2Int(ctx.mkBVNot(ctx.mkInt2BV(BIT_SIZE, expr)), true);
            case NEG:
                return (IntExpr) ctx.mkMul(expr, ctx.mkInt(-1));
            case ABS:
                return (IntExpr) ctx.mkITE(ctx.mkLe(expr, ctx.mkInt(0)), ctx.mkMul(expr, ctx.mkInt(-1)), expr);
            default:
                return ctx.mkInt(0);
        }
    }

    public FuncDecl sum(SumExpression sumExpression) {

        VariableDetector variableDetector = new VariableDetector();
        sumExpression.accept(variableDetector);

        List<Variable> outerVariables = new ArrayList<>(variableDetector.variables());
        List<Variable> declVariables = new ArrayList<>();

        Set<Expression> declExpressionSet = new HashSet<>();
        Set<Formula> declFormulaSet = new HashSet<>();

        sumExpression.decls().forEach(decl -> {
            declVariables.add(decl.variable());
            declExpressionSet.add(decl.expression());
            declFormulaSet.add(decl.variable().in(decl.expression()));
        });

        outerVariables.removeAll(declVariables);

        outerVariables.sort(Comparator.comparingInt(Object::hashCode));

        Map<Variable, Expr> tempMap = new HashMap<>(variableExprMap);

        Expr[] declExprs = new Expr[declVariables.size()];
        Expr[] outerExprs = new Expr[outerVariables.size()];

        for (int i = 0; i < declExprs.length; i++) {
            declExprs[i] = ctx.mkConst("x!" + varCount++, UNIV);
            variableExprMap.put(declVariables.get(i), declExprs[i]);
        }

        for (int i = 0; i < outerExprs.length; i++) {
            outerExprs[i] = ctx.mkConst("x!" + varCount++, UNIV);
            variableExprMap.put(outerVariables.get(i), outerExprs[i]);
        }

        IntExpr generalSum = sumExpression.intExpr().accept(this);

        // **************************************** //

        int inSize = outerVariables.size();
        int outSize = declVariables.size();

        Sort[] inSorts = new Sort[inSize];
        Arrays.fill(inSorts, UNIV);

        FuncDecl sum = ctx.mkFuncDecl("SUM[" + sumExpression.toString() + "]" + varCount++
                , inSorts, ctx.mkIntSort());

        FuncDecl cardinalityFunc = ctx.mkFuncDecl("#[" + sumExpression.toString() + "]" + varCount++
                , inSorts, ctx.mkIntSort());

        Sort[] sumSorts = new Sort[inSize + 1];
        Arrays.fill(sumSorts, UNIV);
        sumSorts[sumSorts.length - 1] = ctx.mkIntSort();

        FuncDecl sumRecursive = ctx.mkFuncDecl("SUM_RECURSIVE[" + sumExpression.toString() + "]" + varCount++
                , sumSorts, ctx.mkIntSort());

        Sort[] ordSorts = new Sort[inSize + outSize];
        Arrays.fill(ordSorts, UNIV);

        FuncDecl ordFunc = ctx.mkFuncDecl("ord[" + sumExpression.toString() + "]" + varCount++, ordSorts, ctx.mkIntSort());

        Expr[] ordExprs = new Expr[ordSorts.length];
        System.arraycopy(outerExprs, 0, ordExprs, 0, inSize);
        System.arraycopy(declExprs, 0, ordExprs, inSize, outSize);

        IntExpr intExpr = ctx.mkIntConst("i!" + varCount++);

        Sort[] invSorts = new Sort[inSize + 1];
        System.arraycopy(inSorts, 0, invSorts, 0, inSize);
        invSorts[invSorts.length - 1] = ctx.mkIntSort();

        Expr[] invExprs = new Expr[inSize + 1];
        System.arraycopy(outerExprs, 0, invExprs, 0, inSize);
        invExprs[invExprs.length - 1] = intExpr;

        // crd = 0 ⇔ ∀f : FSO, ¬isFSO(f )
        // ****************************************** //
        BoolExpr boolExprEqZero = ctx.mkIff(ctx.mkEq(cardinalityFunc.apply(outerExprs), ctx.mkInt(0)), Expression.union(declExpressionSet).no().accept(this));

        if (inSize > 0) {
            boolExprEqZero = ctx.mkForall(outerExprs, boolExprEqZero
                    , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
        }
        // ****************************************** //

        // ∀f : FSO | isFSO(f) ⇒ 1 ≤ ord(f ) ≤ crd
        // ****************************************** //

        BoolExpr boolExprOrd = ctx.mkForall(ordExprs
                , ctx.mkImplies(Formula.and(declFormulaSet).accept(this)
                        , ctx.mkAnd(ctx.mkLe(ctx.mkInt(1), (IntExpr) ordFunc.apply(ordExprs))
                                , ctx.mkLe((IntExpr) ordFunc.apply(ordExprs)
                                        , (IntExpr) cardinalityFunc.apply(outerExprs))))
                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

        // ****************************************** //

        // ∀i : Nat | 1 ≤ i ≤ crd ⇒ isFSO(inv(i))
        // inv = ord^−1
        // ****************************************** //

        BoolExpr boolExprInv = ctx.mkForall(invExprs,
                ctx.mkImplies(ctx.mkAnd(ctx.mkLe(ctx.mkInt(1), intExpr)
                        , ctx.mkLe(intExpr, (IntExpr) cardinalityFunc.apply(outerExprs)))
                        , ctx.mkExists(declExprs, ctx.mkAnd(
                                ctx.mkEq(ordFunc.apply(ordExprs), intExpr)
                                , Formula.and(declFormulaSet).accept(this))
                                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null))
                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

        Expr[] oneToOneExprs = new Expr[inSize + outSize * 2];
        for (int i = 0; i < oneToOneExprs.length; i++) {
            oneToOneExprs[i] = ctx.mkConst("x!" + varCount++, UNIV);
        }

        Expr[] firstOne = new Expr[ordExprs.length];
        System.arraycopy(oneToOneExprs, 0, firstOne, 0, firstOne.length);

        Expr[] secondOne = new Expr[ordExprs.length];
        System.arraycopy(oneToOneExprs, 0, secondOne, 0, inSize);
        System.arraycopy(oneToOneExprs, ordExprs.length, secondOne, inSize, outSize);

        BoolExpr[] eqs = new BoolExpr[outSize];
        for (int i = 0; i < outSize; i++) {
            eqs[i] = ctx.mkEq(firstOne[i + inSize], secondOne[i + inSize]);
        }

        BoolExpr boolExprOneToOne = ctx.mkForall(oneToOneExprs
                , ctx.mkImplies(ctx.mkEq(ordFunc.apply(firstOne), ordFunc.apply(secondOne))
                        , ctx.mkAnd(eqs))
                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

        goal.add(boolExprEqZero);
        goal.add(boolExprOrd);
        goal.add(boolExprInv);
        goal.add(boolExprOneToOne);

        // ****************************************** //

        Expr[] allExprs = new Expr[ordExprs.length + 1];
        System.arraycopy(ordExprs, 0, allExprs, 0, ordExprs.length);
        allExprs[allExprs.length - 1] = intExpr;

        Expr[] sumRecursiveExprsPlus1 = new Expr[invExprs.length];
        System.arraycopy(outerExprs, 0, sumRecursiveExprsPlus1, 0, inSize);
        sumRecursiveExprsPlus1[sumRecursiveExprsPlus1.length - 1] = ctx.mkAdd(intExpr, ctx.mkInt(1));

        FuncDecl generalFunc = ctx.mkFuncDecl("PARTIAL_SUM[" + sumExpression.toString() + "]" + varCount++, invSorts, ctx.mkIntSort());

        BoolExpr boolExprGeneral = ctx.mkForall(allExprs
                        , ctx.mkImplies(ctx.mkEq(ordFunc.apply(ordExprs), intExpr)
                                        , ctx.mkEq(generalFunc.apply(invExprs), generalSum))
                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

        goal.add(boolExprGeneral);

        BoolExpr boolExprSumRecursive = ctx.mkForall(invExprs, ctx.mkEq(sumRecursive.apply(invExprs)
                , ctx.mkITE(ctx.mkAnd(ctx.mkLe(ctx.mkInt(1), intExpr)
                                    , ctx.mkLe(intExpr, (IntExpr) cardinalityFunc.apply(outerExprs)))
                        , ctx.mkAdd((IntExpr) generalFunc.apply(invExprs), (IntExpr) sumRecursive.apply(sumRecursiveExprsPlus1))
                        , ctx.mkInt(0)))
                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

        goal.add(boolExprSumRecursive);

        Expr[] outerExprsPlus1 = new Expr[outerExprs.length + 1];
        System.arraycopy(outerExprs, 0, outerExprsPlus1, 0, outerExprs.length);
        outerExprsPlus1[outerExprsPlus1.length - 1] = ctx.mkInt(1);

        BoolExpr boolExprSum = ctx.mkForall(outerExprs, ctx.mkEq(sum.apply(outerExprs), sumRecursive.apply(outerExprsPlus1))
                , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);

        goal.add(boolExprSum);

        intExprFuncMap.put(sumExpression.toString(), sum);

        variableExprMap = tempMap;

        return sum;
    }

    @Override
    public IntExpr visit(SumExpression sumExpression) {
        VariableDetector variableDetector = new VariableDetector();
        sumExpression.accept(variableDetector);

        List<Variable> outerVariables = new ArrayList<>(variableDetector.variables());

        sumExpression.decls().forEach(decl -> {
            outerVariables.remove(decl.variable());
        });

        outerVariables.sort(Comparator.comparingInt(Object::hashCode));

        Expr[] inExpr = outerVariables.stream().map(v -> variableExprMap.get(v)).toArray(Expr[]::new);

        return (IntExpr) intExprFuncMap.computeIfAbsent(sumExpression.toString(), s -> sum(sumExpression)).apply(inExpr);
    }

    @Override
    public BoolExpr visit(IntComparisonFormula intComparisonFormula) {
        switch (intComparisonFormula.op()) {
            case EQ:
                return ctx.mkEq(intComparisonFormula.left().accept(this)
                        , intComparisonFormula.right().accept(this));
            case GT:
                return ctx.mkGt(intComparisonFormula.left().accept(this)
                        , intComparisonFormula.right().accept(this));
            case LT:
                return ctx.mkLt(intComparisonFormula.left().accept(this)
                        , intComparisonFormula.right().accept(this));
            case GTE:
                return ctx.mkGe(intComparisonFormula.left().accept(this)
                        , intComparisonFormula.right().accept(this));
            case LTE:
                return ctx.mkLe(intComparisonFormula.left().accept(this)
                        , intComparisonFormula.right().accept(this));
            default:
                return ctx.mkFalse();
        }
    }

    @Override
    public BoolExpr visit(QuantifiedFormula quantifiedFormula) {
        int exprsSize = quantifiedFormula.decls().size();

        Expr[] exprs1 = new Expr[exprsSize];
        BoolExpr[] ands = new BoolExpr[exprsSize];

        for (int i = 0; i < exprsSize; i++) {
            Decl decl = quantifiedFormula.decls().get(i);
            exprs1[i] = ctx.mkConst(decl.variable().name(), UNIV);
            variableExprMap.put(decl.variable(), exprs1[i]);
        }
        for (int i = 0; i < exprsSize; i++) {
            Decl decl = quantifiedFormula.decls().get(i);
            ands[i] = decl.variable().in(decl.expression()).accept(this);
        }

        Expr[] temp = exprs;

        exprs = exprs1;
        BoolExpr boolExpr = quantifiedFormula.formula().accept(this);

        exprs = temp;

        switch (quantifiedFormula.quantifier()) {
            case ALL:
                return ctx.mkForall(exprs1
                        , ctx.mkImplies(ctx.mkAnd(ands), boolExpr)
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
            case SOME:
                return ctx.mkExists(exprs1
                        , ctx.mkAnd(ctx.mkAnd(ands), boolExpr)
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), ctx.mkSymbol(skolemPrefix + skolemID++));
            default:
                return ctx.mkFalse();
        }
    }

    @Override
    public BoolExpr visit(NaryFormula formula) {
        switch (formula.op()) {
            case AND:
                BoolExpr[] boolExprs = new BoolExpr[formula.size()];
                for (int i = 0; i < boolExprs.length; i++) {
                    boolExprs[i] = formula.child(i).accept(this);
                }
                return ctx.mkAnd(boolExprs);
            case OR:
                boolExprs = new BoolExpr[formula.size()];
                for (int i = 0; i < boolExprs.length; i++) {
                    boolExprs[i] = formula.child(i).accept(this);
                }
                return ctx.mkOr(boolExprs);
            default:
                return ctx.mkFalse();
        }
    }

    @Override
    public BoolExpr visit(BinaryFormula binFormula) {
        switch (binFormula.op()) {
            case IMPLIES:
                return ctx.mkImplies(binFormula.left().accept(this), binFormula.right().accept(this));
            case IFF:
                return ctx.mkEq(binFormula.left().accept(this), binFormula.right().accept(this));
            case OR:
                return ctx.mkOr(binFormula.left().accept(this), binFormula.right().accept(this));
            case AND:
                return ctx.mkAnd(binFormula.left().accept(this), binFormula.right().accept(this));
            default:
                return ctx.mkFalse();
        }
    }

    @Override
    public BoolExpr visit(NotFormula not) {
        return ctx.mkNot(not.formula().accept(this));
    }

    @Override
    public BoolExpr visit(ConstantFormula constant) {
        return constant.booleanValue() ? ctx.mkTrue() : ctx.mkFalse();
    }

    @Override
    public BoolExpr visit(ComparisonFormula compFormula) {
        switch (compFormula.op()) {
            case EQUALS:
                Expr[] exprs1;
                if (compFormula.left() instanceof Variable) {
                    if (compFormula.right() instanceof Variable) {
                        return ctx.mkEq(variableExprMap.get(compFormula.left()), variableExprMap.get(compFormula.right()));
                    }
                    else {
                        Variable variable = Variable.unary("x!" + varCount++);
                        return variable.eq(compFormula.left()).forAll(variable.oneOf(compFormula.right())).accept(this);
                    }
                }
                else if (compFormula.right() instanceof Variable) {
                    Variable variable = Variable.unary("x!" + varCount++);
                    return variable.eq(compFormula.right()).forAll(variable.oneOf(compFormula.left())).accept(this);
                }

                exprs1 = new Expr[compFormula.left().arity()];
                for (int i = 0; i < exprs1.length; i++) {
                    exprs1[i] = ctx.mkConst("x!" + (varCount++), UNIV);
                }

                Expr[] temp = exprs;

                exprs = exprs1;
                BoolExpr left = compFormula.left().accept(this);
                BoolExpr right = compFormula.right().accept(this);

                exprs = temp;

                return ctx.mkForall(exprs1, ctx.mkEq(left, right)
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
            case SUBSET:
                if (compFormula.left() instanceof Variable) {
                    if (compFormula.right() instanceof Variable) {
                        return ctx.mkEq(variableExprMap.get(compFormula.left()), variableExprMap.get(compFormula.right()));
                    }
                    else {
                        exprs1 = new Expr[compFormula.left().arity()];
                        exprs1[0] = variableExprMap.get(compFormula.left());

                        temp = exprs;

                        exprs = exprs1;
                        BoolExpr boolExpr = compFormula.right().accept(this);

                        exprs = temp;

                        return boolExpr;
                    }
                }
                else if (compFormula.right() instanceof Variable) {
                    Variable variable = Variable.unary("x!" + varCount++);
                    return variable.eq(compFormula.right()).forAll(variable.oneOf(compFormula.left())).accept(this);
                }

                exprs1 = new Expr[compFormula.left().arity()];
                for (int i = 0; i < exprs1.length; i++) {
                    exprs1[i] = ctx.mkConst("x!" + (varCount++), UNIV);
                }

                temp = exprs;

                exprs = exprs1;
                left = compFormula.left().accept(this);
                right = compFormula.right().accept(this);

                exprs = temp;

                return ctx.mkForall(exprs1
                        , ctx.mkImplies(left, right)
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
            default:
                return ctx.mkFalse();
        }
    }

    @Override
    public BoolExpr visit(MultiplicityFormula multiplicityFormula) {
        switch (multiplicityFormula.multiplicity()) {
            case SOME:
                Expr[] exprs1 = new Expr[multiplicityFormula.expression().arity()];
                for (int i = 0; i < exprs1.length; i++) {
                    exprs1[i] = ctx.mkConst("x!" + (varCount++), UNIV);
                }

                Expr[] temp = exprs;

                exprs = exprs1;
                BoolExpr boolExpr = multiplicityFormula.expression().accept(this);

                exprs = temp;

                return ctx.mkExists(exprs1, boolExpr
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), ctx.mkSymbol(skolemPrefix + skolemID++));
            case NO:
                exprs1 = new Expr[multiplicityFormula.expression().arity()];
                if (multiplicityFormula.expression() instanceof IntToExprCast) {
                    for (int i = 0; i < exprs1.length; i++) {
                        exprs1[i] = ctx.mkIntConst("i!" + (varCount++));
                    }
                }
                else {
                    for (int i = 0; i < exprs1.length; i++) {
                        exprs1[i] = ctx.mkConst("x!" + (varCount++), UNIV);
                    }
                }

                temp = exprs;

                exprs = exprs1;
                boolExpr = multiplicityFormula.expression().accept(this);

                exprs = temp;

                return ctx.mkNot(ctx.mkExists(exprs1, boolExpr
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), ctx.mkSymbol(skolemPrefix + skolemID++)));
            case ONE:
                exprs1 = new Expr[multiplicityFormula.expression().arity()];
                for (int i = 0; i < exprs1.length; i++) {
                    exprs1[i] = ctx.mkConst("x!" + (varCount++), UNIV);
                }
                Expr[] exprs2 = new Expr[multiplicityFormula.expression().arity()];
                for (int i = 0; i < exprs2.length; i++) {
                    exprs2[i] = ctx.mkConst("x!" + (varCount++), UNIV);
                }
                BoolExpr[] eqs = new BoolExpr[exprs1.length];
                for (int i = 0; i < eqs.length; i++) {
                    eqs[i] = ctx.mkEq(exprs1[i], exprs2[i]);
                }

                Expr[] allExprs = new Expr[exprs1.length + exprs2.length];
                System.arraycopy(exprs1, 0, allExprs, 0, exprs1.length);
                System.arraycopy(exprs2, 0, allExprs, exprs1.length, exprs2.length);

                temp = exprs;

                exprs = exprs1;
                BoolExpr boolExpr1 = multiplicityFormula.expression().accept(this);
                exprs = exprs2;
                BoolExpr boolExpr2 = multiplicityFormula.expression().accept(this);

                exprs = temp;

                Quantifier lone = ctx.mkForall(allExprs
                        , ctx.mkImplies(ctx.mkAnd(boolExpr1, boolExpr2), ctx.mkAnd(eqs))
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
                Quantifier some = ctx.mkExists(exprs1, boolExpr1
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), ctx.mkSymbol(skolemPrefix + skolemID++));

                return ctx.mkAnd(some, lone);
            case LONE:
                exprs1 = new Expr[multiplicityFormula.expression().arity()];
                for (int i = 0; i < exprs1.length; i++) {
                    exprs1[i] = ctx.mkConst("x!" + (varCount++), UNIV);
                }
                exprs2 = new Expr[multiplicityFormula.expression().arity()];
                for (int i = 0; i < exprs1.length; i++) {
                    exprs2[i] = ctx.mkConst("x!" + (varCount++), UNIV);
                }
                eqs = new BoolExpr[exprs1.length];
                for (int i = 0; i < eqs.length; i++) {
                    eqs[i] = ctx.mkEq(exprs1[i], exprs2[i]);
                }

                allExprs = new Expr[exprs1.length + exprs2.length];
                System.arraycopy(exprs1, 0, allExprs, 0, exprs1.length);
                System.arraycopy(exprs2, 0, allExprs, exprs1.length, exprs2.length);

                temp = exprs;

                exprs = exprs1;
                boolExpr1 = multiplicityFormula.expression().accept(this);
                exprs = exprs2;
                boolExpr2 = multiplicityFormula.expression().accept(this);

                exprs = temp;

                return ctx.mkForall(allExprs
                        , ctx.mkImplies(ctx.mkAnd(boolExpr1, boolExpr2), ctx.mkAnd(eqs))
                        , 0, null, null, ctx.mkSymbol(quantifierPrefix + quantifierID++), null);
            default:
                return ctx.mkFalse();
        }
    }

    @Override
    public BoolExpr visit(RelationPredicate predicate) {
        return predicate.toConstraints().accept(this);
    }
}
