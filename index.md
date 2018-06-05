## Using SMT Solvers in Finding Models and Cores for Relational Logic

We present a tool for finding finite models and cores of constraints expressed in First-order Relational Logic, namely [Alloy](http://alloytools.org/), using SMT solvers. Alloy has become a popular choice in automated software engineering community, exploited in solving different problems of design analysis, program verification, test-case generation, and declarative configuration. Its underlying engine, [KodKod](https://github.com/emina/kodkod), relies on performing a full reduction of a relational logic formula to an equisatisfiable propositional formula, using novel algorithms and techniques in translation and symmetry breaking. However, this eager encoding of relational logic does not benefit from the advantages of the lazy encoding framework, DPLL(T), that is based on an interplay between a modern CDCL-based SAT solver and a theory solver, which is the main technique used in award-winning Satisfiability Modulo Theories (SMT) Solvers such as [Z3](https://github.com/Z3Prover/z3) and [CVC4](https://github.com/CVC4/CVC4). They are particularly good at deciding on combinations of quantifier-free fragments of first-order theories; however, they are increasingly gaining performance in dealing with quantifiers as well. For that reason, our tool provides software engineers a mean to benefit from SMT solvers and their quantifier installation techniques using Relation Logic in the front-end. The tool has been successfully integrated into a platform to facilitate automated reasoning on metamodels and partial models as well as being integrated with Alloy Analyzer itself.

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
## Translation

```haskell
kodkod: (Nil in List)
z3:
(forall ((x!0 univ)) (! (=> (Nil x!0) (List x!0)) :qid q!21))

kodkod: (all l: one List | lone (l . car))
z3:
(forall ((l univ))
  (! (let ((a!1 (forall ((y!1 univ) (z!1 univ))
                  (! (=> (and (car l y!1) (car l z!1)) (and (= y!1 z!1)))
                     :qid q!19))))
       (=> (and (List l)) a!1))
     :qid q!20))

kodkod: (all l: one List | lone (l . cdr))
z3:
(forall ((l univ))
  (! (let ((a!1 (forall ((y!1 univ) (z!1 univ))
                  (! (=> (and (cdr l y!1) (cdr l z!1)) (and (= y!1 z!1)))
                     :qid q!0))))
       (=> (and (List l)) a!1)) :qid q!1))

kodkod: (car in (List -> Object))
z3:
(forall ((x!0 univ) (x!1 univ))
  (! (=> (car x!0 x!1) (and (List x!0) (Object x!1))) :qid q!18))

kodkod: one Nil
z3:
(let ((a!1 (forall ((y!0 univ) (z!0 univ))
             (! (=> (and (Nil y!0) (Nil z!0)) (and (= y!0 z!0))) :qid q!25))))
  (and (exists ((y!0 univ)) (! (Nil y!0) :skolemid s!11 :qid q!26)) a!1))

kodkod: no ((Nil . car) + (Nil . cdr))
z3:
(let ((a!1 (exists ((x!0 univ))
             (! (or (exists ((x!1 univ))
                      (! (and (Nil x!1) (car x!1 x!0)) :skolemid s!8 :qid q!22))
                    (exists ((x!1 univ))
                      (! (and (Nil x!1) (cdr x!1 x!0)) :skolemid s!9 :qid q!23)))
                :skolemid s!10 :qid q!24))))
  (not a!1))

kodkod: (cdr in (List -> List))
z3:
(forall ((x!0 univ) (x!1 univ))
  (! (=> (cdr x!0 x!1) (and (List x!0) (List x!1))) :qid q!12))

kodkod: (all l: one (List - Nil) | (some (l . cdr) && some (l . car)))
z3:
(forall ((l univ))
  (! (=> (and (List l) (not (Nil l)))
         (and (exists ((x!1 univ)) (! (cdr l x!1) :skolemid s!4 :qid q!8))
              (exists ((x!1 univ)) (! (car l x!1) :skolemid s!5 :qid q!9)))) :qid q!10))

kodkod: (all [a: one List, b: one List] | ((a in (b . eq)) <=> 
                        (((a . car) = (b . car)) && ((a . cdr) in ((b . cdr) . eq)))))
z3:
(forall ((a univ) (b univ))
  (! (let ((a!1 (forall ((x!2 univ))
                  (! (=> (cdr a x!2)
                         (exists ((x!3 univ))
                           (! (and (cdr b x!3) (eq x!3 x!2))
                              :skolemid s!7
                              :qid q!15))) :qid q!16))))
     (let ((a!2 (and (forall ((x!2 univ))
                       (! (= (car a x!2) (car b x!2)) :qid q!14)) a!1)))
       (=> (and (List a) (List b)) (= (eq b a) a!2)))) :qid q!17))

kodkod: (all l: one List | (Nil in (l . *cdr)))
z3:
(forall ((l univ))
  (! (=> (and (List l))
         (forall ((x!1 univ))
           (! (let ((a!1 (or (= l x!1)
                     (exists ((x!3 univ))
                       (! (let ((a!1 (or (= x!3 x!1)
                                 (exists ((x!4 univ))
                                   (! (let ((a!1 (or (= x!4 x!1)
                                             (exists ((x!5 univ))
                                               (! (let ((a!1 (or (= x!5 x!1)
                                                                 (exists ((x!6 univ))
                                                                   (! (and (cdr x!5 x!6)
                                                                           (= x!6 x!1))
                                                                      :skolemid s!0
                                                                      :qid q!2)))))
                                                    (and (cdr x!4 x!5) a!1))
                                                  :skolemid s!1
                                                  :qid q!3)))))
                                        (and (cdr x!3 x!4) a!1))
                                      :skolemid s!2
                                      :qid q!4)))))
                            (and (cdr l x!3) a!1))
                          :skolemid s!3
                          :qid q!5)))))
                (=> (Nil x!1) a!1))
              :qid q!6)))
     :qid q!7))

kodkod: (eq in (List -> List))
z3:
(forall ((x!0 univ) (x!1 univ))
  (! (=> (eq x!0 x!1) (and (List x!0) (List x!1))) :qid q!13))

kodkod: no (Object & List)
z3:
(not (exists ((x!0 univ))
       (! (and (Object x!0) (List x!0)) :skolemid s!6 :qid q!11)))
```

## Outcome
```vi
relations: {List=[[List0], [List1], [List2], [List3], [List4], [List5]], eq=[[List0, List0], [List1, List1], [List1, List4], [List2, List2], [List2, List3], [List3, List2], [List3, List3], [List4, List1], [List4, List4], [List5, List5]], car=[[List0, Object1], [List1, Object1], [List2, Object0], [List3, Object0], [List4, Object1]], cdr=[[List0, List5], [List1, List2], [List2, List0], [List3, List0], [List4, List3]], Nil=[[List5]], Object=[[Object0], [Object1]]}
ints: []
---OUTCOME---
SATISFIABLE

---INSTANCE---
relations: {List=[[List0], [List1], [List2], [List3], [List4], [List5]], eq=[[List0, List0], [List1, List1], [List1, List4], [List2, List2], [List2, List3], [List3, List2], [List3, List3], [List4, List1], [List4, List4], [List5, List5]], car=[[List0, Object1], [List1, Object1], [List2, Object0], [List3, Object0], [List4, Object1]], cdr=[[List0, List5], [List1, List2], [List2, List0], [List3, List0], [List4, List3]], Nil=[[List5]], Object=[[Object0], [Object1]]}
ints: []

---STATS---
p cnf 0 0
primary variables: 0
translation time: 990 ms
solving time: 7137 ms
```
