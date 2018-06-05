## Using SMT Solvers in Finding Finite Models and Cores for Relational Logic

We present a tool for finding finite models and cores of constraints expressed in First-order Relational Logic, namely Alloy, using SMT solvers. Alloy has become a popular choice in automated software engineering community, exploited in solving different problems of design analysis, program verification, test-case generation, and declarative configuration. Its underlying engine, KodKod, relies on performing a full reduction of a relational logic formula to an equisatisfiable propositional formula, using novel algorithms and techniques in translation and symmetry breaking. However, this eager encoding of relational logic does not benefit from the advantages of the lazy encoding framework, DPLL(T), that is based on an interplay between a modern CDCL-based SAT solver and a theory solver, which is the main technique used in award-winning Satisfiability Modulo Theories (SMT) Solvers such as Z3 and CVC4. They are particularly good at deciding on combinations of quantifier-free fragments of first-order theories; however, they are increasingly gaining performance in dealing with quantifiers as well. For that reason, our tool provides software engineers a mean to benefit from SMT solvers and their quantifier installation techniques using Relation Logic in the front-end. The tool has been successfully integrated into a platform to facilitate automated reasoning on metamodels and partial models as well as being integrated with Alloy Analyzer itself.

[Screencast](https://youtu.be/tk9zRwSylIo) 

## Example Usage

```java
package kodkod.examples.alloyinecore;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;

import java.util.ArrayList;
import java.util.List;

final class TheoryOfList {

    public static void main(String[] args) {
        TheoryOfList theoryOfList = new TheoryOfList();
        System.out.println(theoryOfList);
    }

    private List<Formula> formulaList;
    private Bounds bounds;
    private Solution solution;

    private TheoryOfList() {
        formulaList = new ArrayList<>();
        solveExample();
    }

    // sig Object
    private Relation Object = Relation.unary("Object");
    // sig List
    private Relation List = Relation.unary("List");
    // one 'sig Nil' extends List
    private Relation  Nil = Relation.unary("Nil");
    // 'car': lone Vehicle
    private Relation car = Relation.binary("car");
    // 'cdr': lone List
    private Relation cdr = Relation.binary("cdr");
    // 'eq': set List
    private Relation eq = Relation.binary("eq");

    private void solveExample() {
        defineDeclarations();
        defineFormulas();
        createBounds();

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.Z3Solver);

        solution = solver.solve(Formula.and(formulaList), bounds);
    }

    private void defineDeclarations() {
        // sig 'Nil extends List'
        formulaList.add(Nil.in(List));

        // no Object & List
        formulaList.add(Object.intersection(List).no());

        // 'one' sig Nil extends List
        formulaList.add(Nil.one());

        // car: lone 'Vehicle'
        formulaList.add(car.in(List.product(Object)));

        // cdr: lone 'List'
        formulaList.add(cdr.in(List.product(List)));

        // eq: set 'List'
        formulaList.add(eq.in(List.product(List)));
    }

    private void defineFormulas() {
        // car: 'lone' Object
        Variable l = Variable.unary("l");
        formulaList.add(l.join(car).lone().forAll(l.oneOf(List)));

        // cdr: 'lone' List
        l = Variable.unary("l");
        formulaList.add(l.join(cdr).lone().forAll(l.oneOf(List)));

        // car: 'set' List -- By default, no need for a formula.

        // no Nil.car + Nil.cdr
        formulaList.add(Nil.join(car).union(Nil.join(cdr)).no());

        // all l: List - Nil | some l.cdr and some l.car
        l = Variable.unary("l");
        formulaList.add(l.join(cdr).some().and(l.join(car).some())
                .forAll(l.oneOf(List.difference(Nil))));

        // all l: List: Nil in l.*cdr
        l = Variable.unary("l");
        formulaList.add(Nil.in(l.join(cdr.reflexiveClosure()))
                .forAll(l.oneOf(List)));

        // fact listEquality { all a, b: List | a in b.eq
        //                      iff (a.car = b.car and a.cdr in b.cdr.eq) }
        Variable a = Variable.unary("a");
        Variable b = Variable.unary("b");
        formulaList.add(a.in(b.join(eq)).iff(a.join(car)
                .eq(b.join(car)).and(a.join(cdr).in(b.join(cdr).join(eq))))
                .forAll(a.oneOf(List).and(b.oneOf(List))));
    }

    private void createBounds() {
        String List0 = "List0";
        String List1 = "List1";
        String List2 = "List2";
        String List3 = "List3";
        String List4 = "List4";
        String List5 = "List5";
        String Object0 = "Object0";
        String Object1 = "Object1";

        Universe universe = new Universe(List0, List1, List2, List3, List4, List5, Object0, Object1);
        TupleFactory tupleFactory = universe.factory();
        bounds = new Bounds(universe);

        // Bound unary relations
        bounds.boundExactly(Object, tupleFactory.setOf(Object0, Object1));
        bounds.boundExactly(List, tupleFactory.setOf(List0, List1, List2, List3, List4, List5));
        bounds.bound(Nil, tupleFactory.setOf(List0, List1, List2, List3, List4, List5));

        // Bound binary relations
        bounds.bound(cdr, tupleFactory.setOf(
                tupleFactory.tuple(List1, List2),
                tupleFactory.tuple(List2, List0),
                tupleFactory.tuple(List4, List3),
                tupleFactory.tuple(List3, List0))
                , bounds.upperBound(List).product(bounds.upperBound(List)));

        bounds.bound(car, tupleFactory.setOf(
                tupleFactory.tuple(List1, Object1),
                tupleFactory.tuple(List2, Object0),
                tupleFactory.tuple(List4, Object1),
                tupleFactory.tuple(List0, Object1),
                tupleFactory.tuple(List3, Object0))
                , bounds.upperBound(List).product(bounds.upperBound(Object)));

        bounds.bound(eq, bounds.upperBound(List).product(bounds.upperBound(List)));
    }

    @Override
    public String toString() { return solution.toString();}
}
```
