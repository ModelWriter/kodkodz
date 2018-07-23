package kodkod.examples.models.algorithm.mutex;

import java.util.Arrays;
import java.util.List;
import kodkod.ast.*;
import kodkod.ast.operator.*;
import kodkod.examples.ExampleMetadata;
import kodkod.instance.*;
import kodkod.engine.*;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.config.Options;

@ExampleMetadata(
        Name = "dijkstra-k-state",
        Note = "",
        IsCheck = true,
        PartialModel = true,
        BinaryRelations = 6,
        TernaryRelations = 1,
        NaryRelations = 0,
        HierarchicalTypes = 1,
        NestedRelationalJoins = 9,
        TransitiveClosure = 2,
        NestedQuantifiers = 1,
        SetCardinality = 2,
        Additions = 0,
        Subtractions = 0,
        Comparison = 22,
        OrderedRelations = 1,
        Constraints = 36
)


public final class dijkstraKStateTwoPrivilegedRun {

    public static void main(String[] args) throws Exception {

        Relation x0 = Relation.unary("Int/min");
        Relation x1 = Relation.unary("Int/zero");
        Relation x2 = Relation.unary("Int/max");
        Relation x3 = Relation.nary("Int/next", 2);
        Relation x4 = Relation.unary("seq/Int");
        Relation x5 = Relation.unary("String");
        Relation x6 = Relation.unary("this/FirstProc");
        Relation x7 = Relation.unary("this/Process remainder");
        Relation x8 = Relation.unary("this/Val");
        Relation x9 = Relation.unary("this/Tick");
        Relation x10 = Relation.unary("to/Ord");
        Relation x11 = Relation.nary("this/Process.rightNeighbor", 2);
        Relation x12 = Relation.nary("this/Val.nextVal", 2);
        Relation x13 = Relation.nary("this/Tick.val", 3);
        Relation x14 = Relation.nary("this/Tick.runs", 2);
        Relation x15 = Relation.nary("this/Tick.priv", 2);
        Relation x16 = Relation.unary("to/Ord.First");
        Relation x17 = Relation.nary("to/Ord.Next", 2);
        Relation x18 = Relation.unary("");

        List<String> atomlist = Arrays.asList(
                "-1", "-2", "-3", "-4", "-5",
                "-6", "-7", "-8", "0", "1", "2",
                "3", "4", "5", "6", "7", "FirstProc$0",
                "Process$0", "Process$1", "Tick$0", "Tick$1", "Tick$2", "Tick$3",
                "Tick$4", "Val$0", "Val$1", "Val$2", "Val$3", "to/Ord$0"
        );

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x0_upper = factory.noneOf(1);
        x0_upper.add(factory.tuple("-8"));
        bounds.boundExactly(x0, x0_upper);

        TupleSet x1_upper = factory.noneOf(1);
        x1_upper.add(factory.tuple("0"));
        bounds.boundExactly(x1, x1_upper);

        TupleSet x2_upper = factory.noneOf(1);
        x2_upper.add(factory.tuple("7"));
        bounds.boundExactly(x2, x2_upper);

        TupleSet x3_upper = factory.noneOf(2);
        x3_upper.add(factory.tuple("-8").product(factory.tuple("-7")));
        x3_upper.add(factory.tuple("-7").product(factory.tuple("-6")));
        x3_upper.add(factory.tuple("-6").product(factory.tuple("-5")));
        x3_upper.add(factory.tuple("-5").product(factory.tuple("-4")));
        x3_upper.add(factory.tuple("-4").product(factory.tuple("-3")));
        x3_upper.add(factory.tuple("-3").product(factory.tuple("-2")));
        x3_upper.add(factory.tuple("-2").product(factory.tuple("-1")));
        x3_upper.add(factory.tuple("-1").product(factory.tuple("0")));
        x3_upper.add(factory.tuple("0").product(factory.tuple("1")));
        x3_upper.add(factory.tuple("1").product(factory.tuple("2")));
        x3_upper.add(factory.tuple("2").product(factory.tuple("3")));
        x3_upper.add(factory.tuple("3").product(factory.tuple("4")));
        x3_upper.add(factory.tuple("4").product(factory.tuple("5")));
        x3_upper.add(factory.tuple("5").product(factory.tuple("6")));
        x3_upper.add(factory.tuple("6").product(factory.tuple("7")));
        bounds.boundExactly(x3, x3_upper);

        TupleSet x4_upper = factory.noneOf(1);
        x4_upper.add(factory.tuple("0"));
        x4_upper.add(factory.tuple("1"));
        x4_upper.add(factory.tuple("2"));
        x4_upper.add(factory.tuple("3"));
        x4_upper.add(factory.tuple("4"));
        bounds.boundExactly(x4, x4_upper);

        TupleSet x5_upper = factory.noneOf(1);
        bounds.boundExactly(x5, x5_upper);

        TupleSet x6_upper = factory.noneOf(1);
        x6_upper.add(factory.tuple("FirstProc$0"));
        bounds.boundExactly(x6, x6_upper);

        TupleSet x7_upper = factory.noneOf(1);
        x7_upper.add(factory.tuple("Process$0"));
        x7_upper.add(factory.tuple("Process$1"));
        bounds.bound(x7, x7_upper);

        TupleSet x8_upper = factory.noneOf(1);
        x8_upper.add(factory.tuple("Val$0"));
        x8_upper.add(factory.tuple("Val$1"));
        x8_upper.add(factory.tuple("Val$2"));
        x8_upper.add(factory.tuple("Val$3"));
        bounds.bound(x8, x8_upper);

        TupleSet x9_upper = factory.noneOf(1);
        x9_upper.add(factory.tuple("Tick$0"));
        x9_upper.add(factory.tuple("Tick$1"));
        x9_upper.add(factory.tuple("Tick$2"));
        x9_upper.add(factory.tuple("Tick$3"));
        x9_upper.add(factory.tuple("Tick$4"));
        bounds.boundExactly(x9, x9_upper);

        TupleSet x10_upper = factory.noneOf(1);
        x10_upper.add(factory.tuple("to/Ord$0"));
        bounds.boundExactly(x10, x10_upper);

        TupleSet x11_upper = factory.noneOf(2);
        x11_upper.add(factory.tuple("FirstProc$0").product(factory.tuple("FirstProc$0")));
        x11_upper.add(factory.tuple("FirstProc$0").product(factory.tuple("Process$0")));
        x11_upper.add(factory.tuple("FirstProc$0").product(factory.tuple("Process$1")));
        x11_upper.add(factory.tuple("Process$0").product(factory.tuple("FirstProc$0")));
        x11_upper.add(factory.tuple("Process$0").product(factory.tuple("Process$0")));
        x11_upper.add(factory.tuple("Process$0").product(factory.tuple("Process$1")));
        x11_upper.add(factory.tuple("Process$1").product(factory.tuple("FirstProc$0")));
        x11_upper.add(factory.tuple("Process$1").product(factory.tuple("Process$0")));
        x11_upper.add(factory.tuple("Process$1").product(factory.tuple("Process$1")));
        bounds.bound(x11, x11_upper);

        TupleSet x12_upper = factory.noneOf(2);
        x12_upper.add(factory.tuple("Val$0").product(factory.tuple("Val$0")));
        x12_upper.add(factory.tuple("Val$0").product(factory.tuple("Val$1")));
        x12_upper.add(factory.tuple("Val$0").product(factory.tuple("Val$2")));
        x12_upper.add(factory.tuple("Val$0").product(factory.tuple("Val$3")));
        x12_upper.add(factory.tuple("Val$1").product(factory.tuple("Val$0")));
        x12_upper.add(factory.tuple("Val$1").product(factory.tuple("Val$1")));
        x12_upper.add(factory.tuple("Val$1").product(factory.tuple("Val$2")));
        x12_upper.add(factory.tuple("Val$1").product(factory.tuple("Val$3")));
        x12_upper.add(factory.tuple("Val$2").product(factory.tuple("Val$0")));
        x12_upper.add(factory.tuple("Val$2").product(factory.tuple("Val$1")));
        x12_upper.add(factory.tuple("Val$2").product(factory.tuple("Val$2")));
        x12_upper.add(factory.tuple("Val$2").product(factory.tuple("Val$3")));
        x12_upper.add(factory.tuple("Val$3").product(factory.tuple("Val$0")));
        x12_upper.add(factory.tuple("Val$3").product(factory.tuple("Val$1")));
        x12_upper.add(factory.tuple("Val$3").product(factory.tuple("Val$2")));
        x12_upper.add(factory.tuple("Val$3").product(factory.tuple("Val$3")));
        bounds.bound(x12, x12_upper);

        TupleSet x13_upper = factory.noneOf(3);
        x13_upper.add(factory.tuple("Tick$0").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$0").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$0").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$0").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$3")));
        x13_upper.add(factory.tuple("Tick$0").product(factory.tuple("Process$0")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$0").product(factory.tuple("Process$0")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$0").product(factory.tuple("Process$0")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$0").product(factory.tuple("Process$0")).product(factory.tuple("Val$3")));
        x13_upper.add(factory.tuple("Tick$0").product(factory.tuple("Process$1")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$0").product(factory.tuple("Process$1")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$0").product(factory.tuple("Process$1")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$0").product(factory.tuple("Process$1")).product(factory.tuple("Val$3")));
        x13_upper.add(factory.tuple("Tick$1").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$1").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$1").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$1").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$3")));
        x13_upper.add(factory.tuple("Tick$1").product(factory.tuple("Process$0")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$1").product(factory.tuple("Process$0")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$1").product(factory.tuple("Process$0")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$1").product(factory.tuple("Process$0")).product(factory.tuple("Val$3")));
        x13_upper.add(factory.tuple("Tick$1").product(factory.tuple("Process$1")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$1").product(factory.tuple("Process$1")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$1").product(factory.tuple("Process$1")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$1").product(factory.tuple("Process$1")).product(factory.tuple("Val$3")));
        x13_upper.add(factory.tuple("Tick$2").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$2").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$2").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$2").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$3")));
        x13_upper.add(factory.tuple("Tick$2").product(factory.tuple("Process$0")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$2").product(factory.tuple("Process$0")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$2").product(factory.tuple("Process$0")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$2").product(factory.tuple("Process$0")).product(factory.tuple("Val$3")));
        x13_upper.add(factory.tuple("Tick$2").product(factory.tuple("Process$1")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$2").product(factory.tuple("Process$1")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$2").product(factory.tuple("Process$1")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$2").product(factory.tuple("Process$1")).product(factory.tuple("Val$3")));
        x13_upper.add(factory.tuple("Tick$3").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$3").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$3").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$3").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$3")));
        x13_upper.add(factory.tuple("Tick$3").product(factory.tuple("Process$0")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$3").product(factory.tuple("Process$0")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$3").product(factory.tuple("Process$0")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$3").product(factory.tuple("Process$0")).product(factory.tuple("Val$3")));
        x13_upper.add(factory.tuple("Tick$3").product(factory.tuple("Process$1")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$3").product(factory.tuple("Process$1")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$3").product(factory.tuple("Process$1")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$3").product(factory.tuple("Process$1")).product(factory.tuple("Val$3")));
        x13_upper.add(factory.tuple("Tick$4").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$4").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$4").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$4").product(factory.tuple("FirstProc$0")).product(factory.tuple("Val$3")));
        x13_upper.add(factory.tuple("Tick$4").product(factory.tuple("Process$0")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$4").product(factory.tuple("Process$0")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$4").product(factory.tuple("Process$0")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$4").product(factory.tuple("Process$0")).product(factory.tuple("Val$3")));
        x13_upper.add(factory.tuple("Tick$4").product(factory.tuple("Process$1")).product(factory.tuple("Val$0")));
        x13_upper.add(factory.tuple("Tick$4").product(factory.tuple("Process$1")).product(factory.tuple("Val$1")));
        x13_upper.add(factory.tuple("Tick$4").product(factory.tuple("Process$1")).product(factory.tuple("Val$2")));
        x13_upper.add(factory.tuple("Tick$4").product(factory.tuple("Process$1")).product(factory.tuple("Val$3")));
        bounds.bound(x13, x13_upper);

        TupleSet x14_upper = factory.noneOf(2);
        x14_upper.add(factory.tuple("Tick$0").product(factory.tuple("FirstProc$0")));
        x14_upper.add(factory.tuple("Tick$0").product(factory.tuple("Process$0")));
        x14_upper.add(factory.tuple("Tick$0").product(factory.tuple("Process$1")));
        x14_upper.add(factory.tuple("Tick$1").product(factory.tuple("FirstProc$0")));
        x14_upper.add(factory.tuple("Tick$1").product(factory.tuple("Process$0")));
        x14_upper.add(factory.tuple("Tick$1").product(factory.tuple("Process$1")));
        x14_upper.add(factory.tuple("Tick$2").product(factory.tuple("FirstProc$0")));
        x14_upper.add(factory.tuple("Tick$2").product(factory.tuple("Process$0")));
        x14_upper.add(factory.tuple("Tick$2").product(factory.tuple("Process$1")));
        x14_upper.add(factory.tuple("Tick$3").product(factory.tuple("FirstProc$0")));
        x14_upper.add(factory.tuple("Tick$3").product(factory.tuple("Process$0")));
        x14_upper.add(factory.tuple("Tick$3").product(factory.tuple("Process$1")));
        x14_upper.add(factory.tuple("Tick$4").product(factory.tuple("FirstProc$0")));
        x14_upper.add(factory.tuple("Tick$4").product(factory.tuple("Process$0")));
        x14_upper.add(factory.tuple("Tick$4").product(factory.tuple("Process$1")));
        bounds.bound(x14, x14_upper);

        TupleSet x15_upper = factory.noneOf(2);
        x15_upper.add(factory.tuple("Tick$0").product(factory.tuple("FirstProc$0")));
        x15_upper.add(factory.tuple("Tick$0").product(factory.tuple("Process$0")));
        x15_upper.add(factory.tuple("Tick$0").product(factory.tuple("Process$1")));
        x15_upper.add(factory.tuple("Tick$1").product(factory.tuple("FirstProc$0")));
        x15_upper.add(factory.tuple("Tick$1").product(factory.tuple("Process$0")));
        x15_upper.add(factory.tuple("Tick$1").product(factory.tuple("Process$1")));
        x15_upper.add(factory.tuple("Tick$2").product(factory.tuple("FirstProc$0")));
        x15_upper.add(factory.tuple("Tick$2").product(factory.tuple("Process$0")));
        x15_upper.add(factory.tuple("Tick$2").product(factory.tuple("Process$1")));
        x15_upper.add(factory.tuple("Tick$3").product(factory.tuple("FirstProc$0")));
        x15_upper.add(factory.tuple("Tick$3").product(factory.tuple("Process$0")));
        x15_upper.add(factory.tuple("Tick$3").product(factory.tuple("Process$1")));
        x15_upper.add(factory.tuple("Tick$4").product(factory.tuple("FirstProc$0")));
        x15_upper.add(factory.tuple("Tick$4").product(factory.tuple("Process$0")));
        x15_upper.add(factory.tuple("Tick$4").product(factory.tuple("Process$1")));
        bounds.bound(x15, x15_upper);

        TupleSet x16_upper = factory.noneOf(1);
        x16_upper.add(factory.tuple("Tick$0"));
        x16_upper.add(factory.tuple("Tick$1"));
        x16_upper.add(factory.tuple("Tick$2"));
        x16_upper.add(factory.tuple("Tick$3"));
        x16_upper.add(factory.tuple("Tick$4"));
        bounds.bound(x16, x16_upper);

        TupleSet x17_upper = factory.noneOf(2);
        x17_upper.add(factory.tuple("Tick$0").product(factory.tuple("Tick$0")));
        x17_upper.add(factory.tuple("Tick$0").product(factory.tuple("Tick$1")));
        x17_upper.add(factory.tuple("Tick$0").product(factory.tuple("Tick$2")));
        x17_upper.add(factory.tuple("Tick$0").product(factory.tuple("Tick$3")));
        x17_upper.add(factory.tuple("Tick$0").product(factory.tuple("Tick$4")));
        x17_upper.add(factory.tuple("Tick$1").product(factory.tuple("Tick$0")));
        x17_upper.add(factory.tuple("Tick$1").product(factory.tuple("Tick$1")));
        x17_upper.add(factory.tuple("Tick$1").product(factory.tuple("Tick$2")));
        x17_upper.add(factory.tuple("Tick$1").product(factory.tuple("Tick$3")));
        x17_upper.add(factory.tuple("Tick$1").product(factory.tuple("Tick$4")));
        x17_upper.add(factory.tuple("Tick$2").product(factory.tuple("Tick$0")));
        x17_upper.add(factory.tuple("Tick$2").product(factory.tuple("Tick$1")));
        x17_upper.add(factory.tuple("Tick$2").product(factory.tuple("Tick$2")));
        x17_upper.add(factory.tuple("Tick$2").product(factory.tuple("Tick$3")));
        x17_upper.add(factory.tuple("Tick$2").product(factory.tuple("Tick$4")));
        x17_upper.add(factory.tuple("Tick$3").product(factory.tuple("Tick$0")));
        x17_upper.add(factory.tuple("Tick$3").product(factory.tuple("Tick$1")));
        x17_upper.add(factory.tuple("Tick$3").product(factory.tuple("Tick$2")));
        x17_upper.add(factory.tuple("Tick$3").product(factory.tuple("Tick$3")));
        x17_upper.add(factory.tuple("Tick$3").product(factory.tuple("Tick$4")));
        x17_upper.add(factory.tuple("Tick$4").product(factory.tuple("Tick$0")));
        x17_upper.add(factory.tuple("Tick$4").product(factory.tuple("Tick$1")));
        x17_upper.add(factory.tuple("Tick$4").product(factory.tuple("Tick$2")));
        x17_upper.add(factory.tuple("Tick$4").product(factory.tuple("Tick$3")));
        x17_upper.add(factory.tuple("Tick$4").product(factory.tuple("Tick$4")));
        bounds.bound(x17, x17_upper);

        TupleSet x18_upper = factory.noneOf(1);
        x18_upper.add(factory.tuple("Tick$0"));
        x18_upper.add(factory.tuple("Tick$1"));
        x18_upper.add(factory.tuple("Tick$2"));
        x18_upper.add(factory.tuple("Tick$3"));
        x18_upper.add(factory.tuple("Tick$4"));
        bounds.bound(x18, x18_upper);

        bounds.boundExactly(-8,factory.range(factory.tuple("-8"),factory.tuple("-8")));
        bounds.boundExactly(-7,factory.range(factory.tuple("-7"),factory.tuple("-7")));
        bounds.boundExactly(-6,factory.range(factory.tuple("-6"),factory.tuple("-6")));
        bounds.boundExactly(-5,factory.range(factory.tuple("-5"),factory.tuple("-5")));
        bounds.boundExactly(-4,factory.range(factory.tuple("-4"),factory.tuple("-4")));
        bounds.boundExactly(-3,factory.range(factory.tuple("-3"),factory.tuple("-3")));
        bounds.boundExactly(-2,factory.range(factory.tuple("-2"),factory.tuple("-2")));
        bounds.boundExactly(-1,factory.range(factory.tuple("-1"),factory.tuple("-1")));
        bounds.boundExactly(0,factory.range(factory.tuple("0"),factory.tuple("0")));
        bounds.boundExactly(1,factory.range(factory.tuple("1"),factory.tuple("1")));
        bounds.boundExactly(2,factory.range(factory.tuple("2"),factory.tuple("2")));
        bounds.boundExactly(3,factory.range(factory.tuple("3"),factory.tuple("3")));
        bounds.boundExactly(4,factory.range(factory.tuple("4"),factory.tuple("4")));
        bounds.boundExactly(5,factory.range(factory.tuple("5"),factory.tuple("5")));
        bounds.boundExactly(6,factory.range(factory.tuple("6"),factory.tuple("6")));
        bounds.boundExactly(7,factory.range(factory.tuple("7"),factory.tuple("7")));

        Variable x22=Variable.unary("TwoPrivileged_this");
        Expression x23=x6.union(x7);
        Decls x21=x22.oneOf(x23);
        Expression x26=x22.join(x11);
        Formula x25=x26.one();
        Formula x27=x26.in(x23);
        Formula x24=x25.and(x27);
        Formula x20=x24.forAll(x21);
        Expression x29=x11.join(Expression.UNIV);
        Formula x28=x29.in(x23);
        Variable x33=Variable.unary("TwoPrivileged_this");
        Decls x32=x33.oneOf(x8);
        Expression x36=x33.join(x12);
        Formula x35=x36.one();
        Formula x37=x36.in(x8);
        Formula x34=x35.and(x37);
        Formula x31=x34.forAll(x32);
        Expression x39=x12.join(Expression.UNIV);
        Formula x38=x39.in(x8);
        Variable x42=Variable.unary("TwoPrivileged_this");
        Decls x41=x42.oneOf(x9);
        Expression x46=x42.join(x13);
        Expression x47=x23.product(x8);
        Formula x45=x46.in(x47);
        Variable x50=Variable.unary("");
        Decls x49=x50.oneOf(x23);
        Expression x53=x50.join(x46);
        Formula x52=x53.one();
        Formula x54=x53.in(x8);
        Formula x51=x52.and(x54);
        Formula x48=x51.forAll(x49);
        Formula x44=x45.and(x48);
        Variable x57=Variable.unary("");
        Decls x56=x57.oneOf(x8);
        Expression x59=x46.join(x57);
        Formula x58=x59.in(x23);
        Formula x55=x58.forAll(x56);
        Formula x43=x44.and(x55);
        Formula x40=x43.forAll(x41);
        Expression x62=x13.join(Expression.UNIV);
        Expression x61=x62.join(Expression.UNIV);
        Formula x60=x61.in(x9);
        Variable x65=Variable.unary("TwoPrivileged_this");
        Decls x64=x65.oneOf(x9);
        Expression x67=x65.join(x14);
        Formula x66=x67.in(x23);
        Formula x63=x66.forAll(x64);
        Expression x69=x14.join(Expression.UNIV);
        Formula x68=x69.in(x9);
        Variable x72=Variable.unary("TwoPrivileged_this");
        Decls x71=x72.oneOf(x9);
        Expression x74=x72.join(x15);
        Formula x73=x74.in(x23);
        Formula x70=x73.forAll(x71);
        Expression x76=x15.join(Expression.UNIV);
        Formula x75=x76.in(x9);
        Variable x79=Variable.unary("TwoPrivileged_this");
        Decls x78=x79.oneOf(x9);
        Expression x81=x79.join(x15);
        Variable x84=Variable.unary("TwoPrivileged_p");
        Decls x83=x84.oneOf(x23);
        Formula x87=x84.eq(x6);
        Expression x90=x79.join(x13);
        Expression x89=x84.join(x90);
        Expression x92=x84.join(x11);
        Expression x93=x79.join(x13);
        Expression x91=x92.join(x93);
        Formula x88=x89.eq(x91);
        Formula x86=x87.implies(x88);
        Formula x95=x87.not();
        Expression x99=x79.join(x13);
        Expression x98=x84.join(x99);
        Expression x101=x84.join(x11);
        Expression x102=x79.join(x13);
        Expression x100=x101.join(x102);
        Formula x97=x98.eq(x100);
        Formula x96=x97.not();
        Formula x94=x95.implies(x96);
        Formula x85=x86.and(x94);
        Expression x82=x85.comprehension(x83);
        Formula x80=x81.eq(x82);
        Formula x77=x80.forAll(x78);
        Expression x105=x10.product(x16);
        Expression x104=x10.join(x105);
        Formula x103=x104.in(x9);
        Expression x108=x10.product(x17);
        Expression x107=x10.join(x108);
        Expression x109=x9.product(x9);
        Formula x106=x107.in(x109);
        Formula x110=x17.totalOrder(x9,x16,x18);
        IntExpression x112=x8.count();
        IntExpression x113=x23.count();
        Formula x111=x112.gt(x113);
        Variable x116=Variable.unary("ring_n");
        Decls x115=x116.oneOf(x23);
        Expression x119=x116.join(x11);
        Formula x118=x119.one();
        Expression x123=x11.closure();
        Expression x131=Expression.INTS.union(x5);
        Expression x130=x131.union(x23);
        Expression x129=x130.union(x8);
        Expression x128=x129.union(x9);
        Expression x127=x128.union(x10);
        Expression x126=x127.product(Expression.UNIV);
        Expression x124=Expression.IDEN.intersection(x126);
        Expression x122=x123.union(x124);
        Expression x121=x116.join(x122);
        Formula x120=x23.in(x121);
        Formula x117=x118.and(x120);
        Formula x114=x117.forAll(x115);
        Variable x135=Variable.unary("ring_n");
        Decls x134=x135.oneOf(x8);
        Expression x138=x135.join(x12);
        Formula x137=x138.one();
        Expression x142=x12.closure();
        Expression x144=x127.product(Expression.UNIV);
        Expression x143=Expression.IDEN.intersection(x144);
        Expression x141=x142.union(x143);
        Expression x140=x135.join(x141);
        Formula x139=x8.in(x140);
        Formula x136=x137.and(x139);
        Formula x133=x136.forAll(x134);
        Variable x147=Variable.unary("TwoPrivileged_tp");
        Expression x150=x17.join(x9);
        Expression x149=x9.difference(x150);
        Expression x148=x9.difference(x149);
        Decls x146=x147.oneOf(x148);
        Variable x153=Variable.unary("TwoPrivileged_p");
        Decls x152=x153.oneOf(x23);
        Expression x158=x147.join(x14);
        Formula x157=x153.in(x158);
        Formula x156=x157.not();
        Expression x162=x147.join(x17);
        Expression x161=x162.join(x13);
        Expression x160=x153.join(x161);
        Expression x164=x147.join(x13);
        Expression x163=x153.join(x164);
        Formula x159=x160.eq(x163);
        Formula x155=x156.implies(x159);
        Formula x166=x156.not();
        Formula x169=x153.eq(x6);
        Expression x174=x153.join(x11);
        Expression x175=x147.join(x13);
        Expression x173=x174.join(x175);
        Formula x172=x163.eq(x173);
        Expression x176=x163.join(x12);
        Expression x171=x172.thenElse(x176,x163);
        Formula x170=x160.eq(x171);
        Formula x168=x169.implies(x170);
        Formula x178=x169.not();
        Formula x182=x163.eq(x173);
        Formula x181=x182.not();
        Expression x180=x181.thenElse(x173,x163);
        Formula x179=x160.eq(x180);
        Formula x177=x178.implies(x179);
        Formula x167=x168.and(x177);
        Formula x165=x166.implies(x167);
        Formula x154=x155.and(x165);
        Formula x151=x154.forAll(x152);
        Formula x145=x151.forAll(x146);
        Variable x186=Variable.unary("BadTick_p1");
        Decls x185=x186.oneOf(x23);
        Variable x188=Variable.unary("BadTick_p2");
        Decls x187=x188.oneOf(x23);
        Decls x184=x185.and(x187);
        Formula x192=x186.eq(x188);
        Formula x191=x192.not();
        Formula x195=x186.eq(x6);
        Expression x198=x16.join(x13);
        Expression x197=x186.join(x198);
        Expression x200=x186.join(x11);
        Expression x201=x16.join(x13);
        Expression x199=x200.join(x201);
        Formula x196=x197.eq(x199);
        Formula x194=x195.implies(x196);
        Formula x203=x195.not();
        Expression x207=x16.join(x13);
        Expression x206=x186.join(x207);
        Expression x209=x186.join(x11);
        Expression x210=x16.join(x13);
        Expression x208=x209.join(x210);
        Formula x205=x206.eq(x208);
        Formula x204=x205.not();
        Formula x202=x203.implies(x204);
        Formula x193=x194.and(x202);
        Formula x190=x191.and(x193);
        Formula x213=x188.eq(x6);
        Expression x216=x16.join(x13);
        Expression x215=x188.join(x216);
        Expression x218=x188.join(x11);
        Expression x219=x16.join(x13);
        Expression x217=x218.join(x219);
        Formula x214=x215.eq(x217);
        Formula x212=x213.implies(x214);
        Formula x221=x213.not();
        Expression x225=x16.join(x13);
        Expression x224=x188.join(x225);
        Expression x227=x188.join(x11);
        Expression x228=x16.join(x13);
        Expression x226=x227.join(x228);
        Formula x223=x224.eq(x226);
        Formula x222=x223.not();
        Formula x220=x221.implies(x222);
        Formula x211=x212.and(x220);
        Formula x189=x190.and(x211);
        Formula x183=x189.forSome(x184);
        Variable x232=Variable.unary("TwoPrivileged_p1");
        Decls x231=x232.oneOf(x23);
        Variable x234=Variable.unary("TwoPrivileged_p2");
        Decls x233=x234.oneOf(x23);
        Variable x236=Variable.unary("TwoPrivileged_t1");
        Expression x237=x9.difference(x16);
        Decls x235=x236.oneOf(x237);
        Variable x239=Variable.unary("TwoPrivileged_t2");
        Decls x238=x239.oneOf(x237);
        Decls x230=x231.and(x233).and(x235).and(x238);
        Formula x243=x232.eq(x234);
        Formula x242=x243.not();
        Formula x246=x232.eq(x6);
        Expression x249=x236.join(x13);
        Expression x248=x232.join(x249);
        Expression x251=x232.join(x11);
        Expression x252=x236.join(x13);
        Expression x250=x251.join(x252);
        Formula x247=x248.eq(x250);
        Formula x245=x246.implies(x247);
        Formula x254=x246.not();
        Expression x258=x236.join(x13);
        Expression x257=x232.join(x258);
        Expression x260=x232.join(x11);
        Expression x261=x236.join(x13);
        Expression x259=x260.join(x261);
        Formula x256=x257.eq(x259);
        Formula x255=x256.not();
        Formula x253=x254.implies(x255);
        Formula x244=x245.and(x253);
        Formula x241=x242.and(x244);
        Formula x264=x234.eq(x6);
        Expression x267=x239.join(x13);
        Expression x266=x234.join(x267);
        Expression x269=x234.join(x11);
        Expression x270=x239.join(x13);
        Expression x268=x269.join(x270);
        Formula x265=x266.eq(x268);
        Formula x263=x264.implies(x265);
        Formula x272=x264.not();
        Expression x276=x239.join(x13);
        Expression x275=x234.join(x276);
        Expression x278=x234.join(x11);
        Expression x279=x239.join(x13);
        Expression x277=x278.join(x279);
        Formula x274=x275.eq(x277);
        Formula x273=x274.not();
        Formula x271=x272.implies(x273);
        Formula x262=x263.and(x271);
        Formula x240=x241.and(x262);
        Formula x229=x240.forSome(x230);
        Formula x280=x0.eq(x0);
        Formula x281=x1.eq(x1);
        Formula x282=x2.eq(x2);
        Formula x283=x3.eq(x3);
        Formula x284=x4.eq(x4);
        Formula x285=x5.eq(x5);
        Formula x286=x6.eq(x6);
        Formula x287=x7.eq(x7);
        Formula x288=x8.eq(x8);
        Formula x289=x9.eq(x9);
        Formula x290=x10.eq(x10);
        Formula x291=x11.eq(x11);
        Formula x292=x12.eq(x12);
        Formula x293=x13.eq(x13);
        Formula x294=x14.eq(x14);
        Formula x295=x15.eq(x15);
        Formula x296=x16.eq(x16);
        Formula x297=x17.eq(x17);
        Formula x298=x18.eq(x18);
        Formula x19=Formula.compose(FormulaOperator.AND, x20, x28, x31, x38, x40, x60, x63, x68, x70, x75, x77, x103, x106, x110, x111, x114, x133, x145, x183, x229, x280, x281, x282, x283, x284, x285, x286, x287, x288, x289, x290, x291, x292, x293, x294, x295, x296, x297, x298);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        //solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);
        System.out.println("Solving...");
        System.out.flush();
        Solution sol = solver.solve(x19,bounds);
        System.out.println(sol.toString());
    }}