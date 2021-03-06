package kodkod.examples.models.simple.games;

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
        Name = "life",
        Note = "",
        IsCheck = false,
        PartialModel = true,
        BinaryRelations = 5,
        TernaryRelations = 0,
        NaryRelations = 0,
        HierarchicalTypes =1,
        NestedRelationalJoins = 7,
        TransitiveClosure = 4,
        NestedQuantifiers = 1,
        SetCardinality = 5,
        Additions = 0,
        Subtractions = 0,
        Comparison = 9,
        OrderedRelations = 1,
        Constraints = 18
)



public final class lifeInterestingRun {

    public static void main(String[] args) throws Exception {

        Relation x0 = Relation.unary("Int/min");
        Relation x1 = Relation.unary("Int/zero");
        Relation x2 = Relation.unary("Int/max");
        Relation x3 = Relation.nary("Int/next", 2);
        Relation x4 = Relation.unary("seq/Int");
        Relation x5 = Relation.unary("String");
        Relation x6 = Relation.unary("this/Root");
        Relation x7 = Relation.unary("this/Point remainder");
        Relation x8 = Relation.unary("this/State");
        Relation x9 = Relation.unary("ord/Ord");
        Relation x10 = Relation.nary("this/Point.right", 2);
        Relation x11 = Relation.nary("this/Point.below", 2);
        Relation x12 = Relation.nary("this/State.live", 2);
        Relation x13 = Relation.unary("ord/Ord.First");
        Relation x14 = Relation.nary("ord/Ord.Next", 2);
        Relation x15 = Relation.unary("");

        List<String> atomlist = Arrays.asList(
                "-1", "-2", "-3", "-4", "-5",
                "-6", "-7", "-8", "0", "1", "2",
                "3", "4", "5", "6", "7", "Point$0",
                "Point$1", "Point$2", "Point$3", "Point$4", "Root$0", "State$0",
                "State$1", "State$2", "ord/Ord$0"
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
        bounds.boundExactly(x4, x4_upper);

        TupleSet x5_upper = factory.noneOf(1);
        bounds.boundExactly(x5, x5_upper);

        TupleSet x6_upper = factory.noneOf(1);
        x6_upper.add(factory.tuple("Root$0"));
        bounds.boundExactly(x6, x6_upper);

        TupleSet x7_upper = factory.noneOf(1);
        x7_upper.add(factory.tuple("Point$0"));
        x7_upper.add(factory.tuple("Point$1"));
        x7_upper.add(factory.tuple("Point$2"));
        x7_upper.add(factory.tuple("Point$3"));
        x7_upper.add(factory.tuple("Point$4"));
        bounds.boundExactly(x7, x7_upper);

        TupleSet x8_upper = factory.noneOf(1);
        x8_upper.add(factory.tuple("State$0"));
        x8_upper.add(factory.tuple("State$1"));
        x8_upper.add(factory.tuple("State$2"));
        bounds.boundExactly(x8, x8_upper);

        TupleSet x9_upper = factory.noneOf(1);
        x9_upper.add(factory.tuple("ord/Ord$0"));
        bounds.boundExactly(x9, x9_upper);

        TupleSet x10_upper = factory.noneOf(2);
        x10_upper.add(factory.tuple("Root$0").product(factory.tuple("Root$0")));
        x10_upper.add(factory.tuple("Root$0").product(factory.tuple("Point$0")));
        x10_upper.add(factory.tuple("Root$0").product(factory.tuple("Point$1")));
        x10_upper.add(factory.tuple("Root$0").product(factory.tuple("Point$2")));
        x10_upper.add(factory.tuple("Root$0").product(factory.tuple("Point$3")));
        x10_upper.add(factory.tuple("Root$0").product(factory.tuple("Point$4")));
        x10_upper.add(factory.tuple("Point$0").product(factory.tuple("Root$0")));
        x10_upper.add(factory.tuple("Point$0").product(factory.tuple("Point$0")));
        x10_upper.add(factory.tuple("Point$0").product(factory.tuple("Point$1")));
        x10_upper.add(factory.tuple("Point$0").product(factory.tuple("Point$2")));
        x10_upper.add(factory.tuple("Point$0").product(factory.tuple("Point$3")));
        x10_upper.add(factory.tuple("Point$0").product(factory.tuple("Point$4")));
        x10_upper.add(factory.tuple("Point$1").product(factory.tuple("Root$0")));
        x10_upper.add(factory.tuple("Point$1").product(factory.tuple("Point$0")));
        x10_upper.add(factory.tuple("Point$1").product(factory.tuple("Point$1")));
        x10_upper.add(factory.tuple("Point$1").product(factory.tuple("Point$2")));
        x10_upper.add(factory.tuple("Point$1").product(factory.tuple("Point$3")));
        x10_upper.add(factory.tuple("Point$1").product(factory.tuple("Point$4")));
        x10_upper.add(factory.tuple("Point$2").product(factory.tuple("Root$0")));
        x10_upper.add(factory.tuple("Point$2").product(factory.tuple("Point$0")));
        x10_upper.add(factory.tuple("Point$2").product(factory.tuple("Point$1")));
        x10_upper.add(factory.tuple("Point$2").product(factory.tuple("Point$2")));
        x10_upper.add(factory.tuple("Point$2").product(factory.tuple("Point$3")));
        x10_upper.add(factory.tuple("Point$2").product(factory.tuple("Point$4")));
        x10_upper.add(factory.tuple("Point$3").product(factory.tuple("Root$0")));
        x10_upper.add(factory.tuple("Point$3").product(factory.tuple("Point$0")));
        x10_upper.add(factory.tuple("Point$3").product(factory.tuple("Point$1")));
        x10_upper.add(factory.tuple("Point$3").product(factory.tuple("Point$2")));
        x10_upper.add(factory.tuple("Point$3").product(factory.tuple("Point$3")));
        x10_upper.add(factory.tuple("Point$3").product(factory.tuple("Point$4")));
        x10_upper.add(factory.tuple("Point$4").product(factory.tuple("Root$0")));
        x10_upper.add(factory.tuple("Point$4").product(factory.tuple("Point$0")));
        x10_upper.add(factory.tuple("Point$4").product(factory.tuple("Point$1")));
        x10_upper.add(factory.tuple("Point$4").product(factory.tuple("Point$2")));
        x10_upper.add(factory.tuple("Point$4").product(factory.tuple("Point$3")));
        x10_upper.add(factory.tuple("Point$4").product(factory.tuple("Point$4")));
        bounds.bound(x10, x10_upper);

        TupleSet x11_upper = factory.noneOf(2);
        x11_upper.add(factory.tuple("Root$0").product(factory.tuple("Root$0")));
        x11_upper.add(factory.tuple("Root$0").product(factory.tuple("Point$0")));
        x11_upper.add(factory.tuple("Root$0").product(factory.tuple("Point$1")));
        x11_upper.add(factory.tuple("Root$0").product(factory.tuple("Point$2")));
        x11_upper.add(factory.tuple("Root$0").product(factory.tuple("Point$3")));
        x11_upper.add(factory.tuple("Root$0").product(factory.tuple("Point$4")));
        x11_upper.add(factory.tuple("Point$0").product(factory.tuple("Root$0")));
        x11_upper.add(factory.tuple("Point$0").product(factory.tuple("Point$0")));
        x11_upper.add(factory.tuple("Point$0").product(factory.tuple("Point$1")));
        x11_upper.add(factory.tuple("Point$0").product(factory.tuple("Point$2")));
        x11_upper.add(factory.tuple("Point$0").product(factory.tuple("Point$3")));
        x11_upper.add(factory.tuple("Point$0").product(factory.tuple("Point$4")));
        x11_upper.add(factory.tuple("Point$1").product(factory.tuple("Root$0")));
        x11_upper.add(factory.tuple("Point$1").product(factory.tuple("Point$0")));
        x11_upper.add(factory.tuple("Point$1").product(factory.tuple("Point$1")));
        x11_upper.add(factory.tuple("Point$1").product(factory.tuple("Point$2")));
        x11_upper.add(factory.tuple("Point$1").product(factory.tuple("Point$3")));
        x11_upper.add(factory.tuple("Point$1").product(factory.tuple("Point$4")));
        x11_upper.add(factory.tuple("Point$2").product(factory.tuple("Root$0")));
        x11_upper.add(factory.tuple("Point$2").product(factory.tuple("Point$0")));
        x11_upper.add(factory.tuple("Point$2").product(factory.tuple("Point$1")));
        x11_upper.add(factory.tuple("Point$2").product(factory.tuple("Point$2")));
        x11_upper.add(factory.tuple("Point$2").product(factory.tuple("Point$3")));
        x11_upper.add(factory.tuple("Point$2").product(factory.tuple("Point$4")));
        x11_upper.add(factory.tuple("Point$3").product(factory.tuple("Root$0")));
        x11_upper.add(factory.tuple("Point$3").product(factory.tuple("Point$0")));
        x11_upper.add(factory.tuple("Point$3").product(factory.tuple("Point$1")));
        x11_upper.add(factory.tuple("Point$3").product(factory.tuple("Point$2")));
        x11_upper.add(factory.tuple("Point$3").product(factory.tuple("Point$3")));
        x11_upper.add(factory.tuple("Point$3").product(factory.tuple("Point$4")));
        x11_upper.add(factory.tuple("Point$4").product(factory.tuple("Root$0")));
        x11_upper.add(factory.tuple("Point$4").product(factory.tuple("Point$0")));
        x11_upper.add(factory.tuple("Point$4").product(factory.tuple("Point$1")));
        x11_upper.add(factory.tuple("Point$4").product(factory.tuple("Point$2")));
        x11_upper.add(factory.tuple("Point$4").product(factory.tuple("Point$3")));
        x11_upper.add(factory.tuple("Point$4").product(factory.tuple("Point$4")));
        bounds.bound(x11, x11_upper);

        TupleSet x12_upper = factory.noneOf(2);
        x12_upper.add(factory.tuple("State$0").product(factory.tuple("Root$0")));
        x12_upper.add(factory.tuple("State$0").product(factory.tuple("Point$0")));
        x12_upper.add(factory.tuple("State$0").product(factory.tuple("Point$1")));
        x12_upper.add(factory.tuple("State$0").product(factory.tuple("Point$2")));
        x12_upper.add(factory.tuple("State$0").product(factory.tuple("Point$3")));
        x12_upper.add(factory.tuple("State$0").product(factory.tuple("Point$4")));
        x12_upper.add(factory.tuple("State$1").product(factory.tuple("Root$0")));
        x12_upper.add(factory.tuple("State$1").product(factory.tuple("Point$0")));
        x12_upper.add(factory.tuple("State$1").product(factory.tuple("Point$1")));
        x12_upper.add(factory.tuple("State$1").product(factory.tuple("Point$2")));
        x12_upper.add(factory.tuple("State$1").product(factory.tuple("Point$3")));
        x12_upper.add(factory.tuple("State$1").product(factory.tuple("Point$4")));
        x12_upper.add(factory.tuple("State$2").product(factory.tuple("Root$0")));
        x12_upper.add(factory.tuple("State$2").product(factory.tuple("Point$0")));
        x12_upper.add(factory.tuple("State$2").product(factory.tuple("Point$1")));
        x12_upper.add(factory.tuple("State$2").product(factory.tuple("Point$2")));
        x12_upper.add(factory.tuple("State$2").product(factory.tuple("Point$3")));
        x12_upper.add(factory.tuple("State$2").product(factory.tuple("Point$4")));
        bounds.bound(x12, x12_upper);

        TupleSet x13_upper = factory.noneOf(1);
        x13_upper.add(factory.tuple("State$0"));
        x13_upper.add(factory.tuple("State$1"));
        x13_upper.add(factory.tuple("State$2"));
        bounds.bound(x13, x13_upper);

        TupleSet x14_upper = factory.noneOf(2);
        x14_upper.add(factory.tuple("State$0").product(factory.tuple("State$0")));
        x14_upper.add(factory.tuple("State$0").product(factory.tuple("State$1")));
        x14_upper.add(factory.tuple("State$0").product(factory.tuple("State$2")));
        x14_upper.add(factory.tuple("State$1").product(factory.tuple("State$0")));
        x14_upper.add(factory.tuple("State$1").product(factory.tuple("State$1")));
        x14_upper.add(factory.tuple("State$1").product(factory.tuple("State$2")));
        x14_upper.add(factory.tuple("State$2").product(factory.tuple("State$0")));
        x14_upper.add(factory.tuple("State$2").product(factory.tuple("State$1")));
        x14_upper.add(factory.tuple("State$2").product(factory.tuple("State$2")));
        bounds.bound(x14, x14_upper);

        TupleSet x15_upper = factory.noneOf(1);
        x15_upper.add(factory.tuple("State$0"));
        x15_upper.add(factory.tuple("State$1"));
        x15_upper.add(factory.tuple("State$2"));
        bounds.bound(x15, x15_upper);

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

        Variable x19=Variable.unary("interesting_this");
        Expression x20=x6.union(x7);
        Decls x18=x19.oneOf(x20);
        Expression x23=x19.join(x10);
        Formula x22=x23.lone();
        Formula x24=x23.in(x20);
        Formula x21=x22.and(x24);
        Formula x17=x21.forAll(x18);
        Expression x26=x10.join(Expression.UNIV);
        Formula x25=x26.in(x20);
        Variable x30=Variable.unary("interesting_this");
        Decls x29=x30.oneOf(x20);
        Expression x33=x30.join(x11);
        Formula x32=x33.lone();
        Formula x34=x33.in(x20);
        Formula x31=x32.and(x34);
        Formula x28=x31.forAll(x29);
        Expression x36=x11.join(Expression.UNIV);
        Formula x35=x36.in(x20);
        Variable x39=Variable.unary("interesting_this");
        Decls x38=x39.oneOf(x8);
        Expression x41=x39.join(x12);
        Formula x40=x41.in(x20);
        Formula x37=x40.forAll(x38);
        Expression x43=x12.join(Expression.UNIV);
        Formula x42=x43.in(x8);
        Expression x46=x9.product(x13);
        Expression x45=x9.join(x46);
        Formula x44=x45.in(x8);
        Expression x49=x9.product(x14);
        Expression x48=x9.join(x49);
        Expression x50=x8.product(x8);
        Formula x47=x48.in(x50);
        Formula x51=x14.totalOrder(x8,x13,x15);
        Variable x54=Variable.unary("interesting_p");
        Decls x53=x54.oneOf(x20);
        Expression x59=x10.union(x11);
        Expression x58=x59.closure();
        Expression x57=x54.join(x58);
        Formula x56=x54.in(x57);
        Formula x55=x56.not();
        Formula x52=x55.forAll(x53);
        Variable x62=Variable.unary("interesting_p");
        Decls x61=x62.oneOf(x20);
        Expression x66=x62.join(x11);
        Expression x65=x66.join(x10);
        Expression x68=x62.join(x10);
        Expression x67=x68.join(x11);
        Formula x64=x65.eq(x67);
        Expression x73=x62.join(x11);
        Formula x72=x73.some();
        Expression x75=x62.join(x10);
        Formula x74=x75.some();
        Formula x71=x72.and(x74);
        Formula x70=x71.not();
        Expression x78=x62.join(x11);
        Expression x77=x78.join(x10);
        Formula x76=x77.some();
        Formula x69=x70.or(x76);
        Formula x63=x64.and(x69);
        Formula x60=x63.forAll(x61);
        Variable x81=Variable.unary("interesting_p");
        Expression x82=x20.difference(x6);
        Decls x80=x81.oneOf(x82);
        Expression x87=x11.transpose();
        Expression x86=x81.join(x87);
        Formula x85=x86.no();
        Formula x84=x85.not();
        Expression x92=x11.closure();
        Expression x99=Expression.INTS.union(x5);
        Expression x98=x99.union(x20);
        Expression x97=x98.union(x8);
        Expression x96=x97.union(x9);
        Expression x95=x96.product(Expression.UNIV);
        Expression x93=Expression.IDEN.intersection(x95);
        Expression x91=x92.union(x93);
        Expression x90=x81.join(x91);
        IntExpression x89=x90.count();
        Expression x104=x11.closure();
        Expression x106=x96.product(Expression.UNIV);
        Expression x105=Expression.IDEN.intersection(x106);
        Expression x103=x104.union(x105);
        Expression x102=x6.join(x103);
        IntExpression x101=x102.count();
        Formula x88=x89.eq(x101);
        Formula x83=x84.or(x88);
        Formula x79=x83.forAll(x80);
        Expression x111=x10.union(x11);
        Expression x110=x111.closure();
        Expression x113=x96.product(Expression.UNIV);
        Expression x112=Expression.IDEN.intersection(x113);
        Expression x109=x110.union(x112);
        Expression x108=x6.join(x109);
        Formula x107=x108.eq(x20);
        Variable x116=Variable.unary("interesting_pre");
        Expression x119=x14.join(x8);
        Expression x118=x8.difference(x119);
        Expression x117=x8.difference(x118);
        Decls x115=x116.oneOf(x117);
        Variable x122=Variable.unary("interesting_p");
        Decls x121=x122.oneOf(x20);
        Expression x128=x116.join(x12);
        Formula x127=x122.in(x128);
        Formula x126=x127.not();
        Expression x139=x122.join(x10);
        Expression x141=x122.join(x10);
        Expression x140=x141.join(x11);
        Expression x138=x139.union(x140);
        Expression x142=x122.join(x11);
        Expression x137=x138.union(x142);
        Expression x144=x122.join(x11);
        Expression x145=x10.transpose();
        Expression x143=x144.join(x145);
        Expression x136=x137.union(x143);
        Expression x147=x10.transpose();
        Expression x146=x122.join(x147);
        Expression x135=x136.union(x146);
        Expression x150=x10.transpose();
        Expression x149=x122.join(x150);
        Expression x151=x11.transpose();
        Expression x148=x149.join(x151);
        Expression x134=x135.union(x148);
        Expression x153=x11.transpose();
        Expression x152=x122.join(x153);
        Expression x133=x134.union(x152);
        Expression x156=x11.transpose();
        Expression x155=x122.join(x156);
        Expression x154=x155.join(x10);
        Expression x132=x133.union(x154);
        Expression x157=x116.join(x12);
        Expression x131=x132.intersection(x157);
        IntExpression x130=x131.count();
        IntExpression x158=IntConstant.constant(3);
        Formula x129=x130.eq(x158);
        Formula x125=x126.and(x129);
        Expression x161=x116.join(x14);
        Expression x160=x161.join(x12);
        Formula x159=x122.in(x160);
        Formula x124=x125.implies(x159);
        Formula x163=x125.not();
        Expression x168=x116.join(x12);
        Formula x167=x122.in(x168);
        IntExpression x171=x131.count();
        IntExpression x172=IntConstant.constant(2);
        Formula x170=x171.eq(x172);
        IntExpression x174=x131.count();
        IntExpression x175=IntConstant.constant(3);
        Formula x173=x174.eq(x175);
        Formula x169=x170.or(x173);
        Formula x166=x167.and(x169);
        Expression x177=x161.join(x12);
        Formula x176=x122.in(x177);
        Formula x165=x166.implies(x176);
        Formula x179=x166.not();
        Expression x182=x161.join(x12);
        Formula x181=x122.in(x182);
        Formula x180=x181.not();
        Formula x178=x179.implies(x180);
        Formula x164=x165.and(x178);
        Formula x162=x163.implies(x164);
        Formula x123=x124.and(x162);
        Formula x120=x123.forAll(x121);
        Formula x114=x120.forAll(x115);
        Expression x184=x8.join(x12);
        Formula x183=x184.some();
        Expression x187=x8.join(x12);
        Expression x186=x20.difference(x187);
        Formula x185=x186.some();
        Formula x188=x10.some();
        Formula x189=x11.some();
        Formula x190=x0.eq(x0);
        Formula x191=x1.eq(x1);
        Formula x192=x2.eq(x2);
        Formula x193=x3.eq(x3);
        Formula x194=x4.eq(x4);
        Formula x195=x5.eq(x5);
        Formula x196=x6.eq(x6);
        Formula x197=x7.eq(x7);
        Formula x198=x8.eq(x8);
        Formula x199=x9.eq(x9);
        Formula x200=x10.eq(x10);
        Formula x201=x11.eq(x11);
        Formula x202=x12.eq(x12);
        Formula x203=x13.eq(x13);
        Formula x204=x14.eq(x14);
        Formula x205=x15.eq(x15);
        Formula x16=Formula.compose(FormulaOperator.AND, x17, x25, x28, x35, x37, x42, x44, x47, x51, x52, x60, x79, x107, x114, x183, x185, x188, x189, x190, x191, x192, x193, x194, x195, x196, x197, x198, x199, x200, x201, x202, x203, x204, x205);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.MiniSat);
        solver.options().setBitwidth(4);
       // solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);
        System.out.println("Solving...");
        System.out.flush();
        Solution sol = solver.solve(x16,bounds);
        System.out.println(sol.toString());
    }}