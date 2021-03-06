package kodkod.examples.models.softwareAbstractions.chapter4;

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
        Name = "grandpa3",
        Note = "",
        IsCheck = true,
        PartialModel = true,
        BinaryRelations = 5,
        TernaryRelations =0,
        NaryRelations = 0,
        HierarchicalTypes =2,
        NestedRelationalJoins = 2,
        TransitiveClosure = 2,
        NestedQuantifiers = 2,
        SetCardinality = 0,
        Additions = 0,
        Subtractions = 0,
        Comparison = 4,
        OrderedRelations = 0,
        Constraints = 9
)



public final class grandpa3OwnGrandpaRun {

    public static void main(String[] args) throws Exception {

        Relation x0 = Relation.unary("Int/min");
        Relation x1 = Relation.unary("Int/zero");
        Relation x2 = Relation.unary("Int/max");
        Relation x3 = Relation.nary("Int/next", 2);
        Relation x4 = Relation.unary("seq/Int");
        Relation x5 = Relation.unary("String");
        Relation x6 = Relation.unary("this/Man");
        Relation x7 = Relation.unary("this/Woman");
        Relation x8 = Relation.nary("this/Person.father", 2);
        Relation x9 = Relation.nary("this/Person.mother", 2);
        Relation x10 = Relation.nary("this/Man.wife", 2);
        Relation x11 = Relation.nary("this/Woman.husband", 2);

        List<String> atomlist = Arrays.asList(
                "-1", "-2", "-3", "-4", "-5",
                "-6", "-7", "-8", "0", "1", "2",
                "3", "4", "5", "6", "7", "Person$0",
                "Person$1", "Person$2", "Person$3"
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
        x6_upper.add(factory.tuple("Person$0"));
        x6_upper.add(factory.tuple("Person$1"));
        x6_upper.add(factory.tuple("Person$2"));
        x6_upper.add(factory.tuple("Person$3"));
        bounds.bound(x6, x6_upper);

        TupleSet x7_upper = factory.noneOf(1);
        x7_upper.add(factory.tuple("Person$0"));
        x7_upper.add(factory.tuple("Person$1"));
        x7_upper.add(factory.tuple("Person$2"));
        x7_upper.add(factory.tuple("Person$3"));
        bounds.bound(x7, x7_upper);

        TupleSet x8_upper = factory.noneOf(2);
        x8_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$0")));
        x8_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$1")));
        x8_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$2")));
        x8_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$3")));
        x8_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$0")));
        x8_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$1")));
        x8_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$2")));
        x8_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$3")));
        x8_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$0")));
        x8_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$1")));
        x8_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$2")));
        x8_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$3")));
        x8_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$0")));
        x8_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$1")));
        x8_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$2")));
        x8_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$3")));
        bounds.bound(x8, x8_upper);

        TupleSet x9_upper = factory.noneOf(2);
        x9_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$0")));
        x9_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$1")));
        x9_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$2")));
        x9_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$3")));
        x9_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$0")));
        x9_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$1")));
        x9_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$2")));
        x9_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$3")));
        x9_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$0")));
        x9_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$1")));
        x9_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$2")));
        x9_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$3")));
        x9_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$0")));
        x9_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$1")));
        x9_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$2")));
        x9_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$3")));
        bounds.bound(x9, x9_upper);

        TupleSet x10_upper = factory.noneOf(2);
        x10_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$0")));
        x10_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$1")));
        x10_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$2")));
        x10_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$3")));
        x10_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$0")));
        x10_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$1")));
        x10_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$2")));
        x10_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$3")));
        x10_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$0")));
        x10_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$1")));
        x10_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$2")));
        x10_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$3")));
        x10_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$0")));
        x10_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$1")));
        x10_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$2")));
        x10_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$3")));
        bounds.bound(x10, x10_upper);

        TupleSet x11_upper = factory.noneOf(2);
        x11_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$0")));
        x11_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$1")));
        x11_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$2")));
        x11_upper.add(factory.tuple("Person$0").product(factory.tuple("Person$3")));
        x11_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$0")));
        x11_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$1")));
        x11_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$2")));
        x11_upper.add(factory.tuple("Person$1").product(factory.tuple("Person$3")));
        x11_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$0")));
        x11_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$1")));
        x11_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$2")));
        x11_upper.add(factory.tuple("Person$2").product(factory.tuple("Person$3")));
        x11_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$0")));
        x11_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$1")));
        x11_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$2")));
        x11_upper.add(factory.tuple("Person$3").product(factory.tuple("Person$3")));
        bounds.bound(x11, x11_upper);

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

        Expression x14=x6.intersection(x7);
        Formula x13=x14.no();
        Variable x17=Variable.unary("ownGrandpa_this");
        Decls x16=x17.oneOf(x6);
        Expression x20=x17.join(x10);
        Formula x19=x20.lone();
        Formula x21=x20.in(x7);
        Formula x18=x19.and(x21);
        Formula x15=x18.forAll(x16);
        Expression x23=x10.join(Expression.UNIV);
        Formula x22=x23.in(x6);
        Variable x27=Variable.unary("ownGrandpa_this");
        Decls x26=x27.oneOf(x7);
        Expression x30=x27.join(x11);
        Formula x29=x30.lone();
        Formula x31=x30.in(x6);
        Formula x28=x29.and(x31);
        Formula x25=x28.forAll(x26);
        Expression x33=x11.join(Expression.UNIV);
        Formula x32=x33.in(x7);
        Variable x36=Variable.unary("ownGrandpa_this");
        Expression x37=x6.union(x7);
        Decls x35=x36.oneOf(x37);
        Expression x40=x36.join(x8);
        Formula x39=x40.lone();
        Formula x41=x40.in(x6);
        Formula x38=x39.and(x41);
        Formula x34=x38.forAll(x35);
        Expression x43=x8.join(Expression.UNIV);
        Formula x42=x43.in(x37);
        Variable x46=Variable.unary("ownGrandpa_this");
        Decls x45=x46.oneOf(x37);
        Expression x49=x46.join(x9);
        Formula x48=x49.lone();
        Formula x50=x49.in(x7);
        Formula x47=x48.and(x50);
        Formula x44=x47.forAll(x45);
        Expression x52=x9.join(Expression.UNIV);
        Formula x51=x52.in(x37);
        Variable x55=Variable.unary("ownGrandpa_p");
        Decls x54=x55.oneOf(x37);
        Expression x60=x9.union(x8);
        Expression x59=x60.closure();
        Expression x58=x55.join(x59);
        Formula x57=x55.in(x58);
        Formula x56=x57.not();
        Formula x53=x56.forAll(x54);
        Expression x62=x11.transpose();
        Formula x61=x10.eq(x62);
        Expression x65=x10.union(x11);
        Expression x67=x9.union(x8);
        Expression x66=x67.closure();
        Expression x64=x65.intersection(x66);
        Formula x63=x64.no();
        Variable x70=Variable.unary("ownGrandpa_p");
        Decls x69=x70.oneOf(x37);
        Expression x77=x9.union(x8);
        Expression x78=x8.join(x10);
        Expression x76=x77.union(x78);
        Expression x79=x9.join(x11);
        Expression x75=x76.union(x79);
        Expression x74=x70.join(x75);
        Expression x73=x74.join(x75);
        Expression x72=x73.intersection(x6);
        Formula x71=x70.in(x72);
        Formula x68=x71.forSome(x69);
        Formula x80=x0.eq(x0);
        Formula x81=x1.eq(x1);
        Formula x82=x2.eq(x2);
        Formula x83=x3.eq(x3);
        Formula x84=x4.eq(x4);
        Formula x85=x5.eq(x5);
        Formula x86=x6.eq(x6);
        Formula x87=x7.eq(x7);
        Formula x88=x8.eq(x8);
        Formula x89=x9.eq(x9);
        Formula x90=x10.eq(x10);
        Formula x91=x11.eq(x11);
        Formula x12=Formula.compose(FormulaOperator.AND, x13, x15, x22, x25, x32, x34, x42, x44, x51, x53, x61, x63, x68, x80, x81, x82, x83, x84, x85, x86, x87, x88, x89, x90, x91);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.MiniSat);
        solver.options().setBitwidth(4);
        //solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);
        System.out.println("Solving...");
        System.out.flush();
        Solution sol = solver.solve(x12,bounds);
        System.out.println(sol.toString());
    }}