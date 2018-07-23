package kodkod.examples.models.softwareAbstractions.chapter6;

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
        Name = "mediaAssets",
        Note = "",
        IsCheck = true,
        PartialModel = true,
        BinaryRelations = 8,
        TernaryRelations =1,
        NaryRelations = 0,
        HierarchicalTypes =0,
        NestedRelationalJoins = 7,
        TransitiveClosure = 0,
        NestedQuantifiers = 0,
        SetCardinality = 0,
        Additions = 0,
        Subtractions = 0,
        Comparison = 35,
        OrderedRelations = 0,
        Constraints = 48
)


public final class mediaAssetsNoBadEntryCheck {

    public static void main(String[] args) throws Exception {

        Relation x0 = Relation.unary("Int/min");
        Relation x1 = Relation.unary("Int/zero");
        Relation x2 = Relation.unary("Int/max");
        Relation x3 = Relation.nary("Int/next", 2);
        Relation x4 = Relation.unary("seq/Int");
        Relation x5 = Relation.unary("String");
        Relation x6 = Relation.unary("this/ApplicationState");
        Relation x7 = Relation.unary("this/Catalog");
        Relation x8 = Relation.unary("this/Asset");
        Relation x9 = Relation.unary("this/CatalogState");
        Relation x10 = Relation.unary("this/Undefined");
        Relation x11 = Relation.nary("this/ApplicationState.catalogs", 2);
        Relation x12 = Relation.nary("this/ApplicationState.catalogState", 3);
        Relation x13 = Relation.nary("this/ApplicationState.currentCatalog", 2);
        Relation x14 = Relation.nary("this/ApplicationState.buffer", 2);
        Relation x15 = Relation.nary("this/CatalogState.assets", 2);
        Relation x16 = Relation.nary("this/CatalogState.hidden", 2);
        Relation x17 = Relation.nary("this/CatalogState.showing", 2);
        Relation x18 = Relation.nary("this/CatalogState.selection", 2);

        List<String> atomlist = Arrays.asList(
                "-1", "-2", "-3", "-4", "-5",
                "-6", "-7", "-8", "0", "1", "2",
                "3", "4", "5", "6", "7", "ApplicationState$0",
                "ApplicationState$1", "ApplicationState$2", "Asset$0", "Asset$1", "Asset$2", "Catalog$0",
                "Catalog$1", "Catalog$2", "CatalogState$0", "CatalogState$1", "CatalogState$2", "Undefined$0"
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
        x6_upper.add(factory.tuple("ApplicationState$0"));
        x6_upper.add(factory.tuple("ApplicationState$1"));
        x6_upper.add(factory.tuple("ApplicationState$2"));
        bounds.bound(x6, x6_upper);

        TupleSet x7_upper = factory.noneOf(1);
        x7_upper.add(factory.tuple("Catalog$0"));
        x7_upper.add(factory.tuple("Catalog$1"));
        x7_upper.add(factory.tuple("Catalog$2"));
        bounds.bound(x7, x7_upper);

        TupleSet x8_upper = factory.noneOf(1);
        x8_upper.add(factory.tuple("Asset$0"));
        x8_upper.add(factory.tuple("Asset$1"));
        x8_upper.add(factory.tuple("Asset$2"));
        bounds.bound(x8, x8_upper);

        TupleSet x9_upper = factory.noneOf(1);
        x9_upper.add(factory.tuple("CatalogState$0"));
        x9_upper.add(factory.tuple("CatalogState$1"));
        x9_upper.add(factory.tuple("CatalogState$2"));
        bounds.bound(x9, x9_upper);

        TupleSet x10_upper = factory.noneOf(1);
        x10_upper.add(factory.tuple("Undefined$0"));
        bounds.boundExactly(x10, x10_upper);

        TupleSet x11_upper = factory.noneOf(2);
        x11_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$0")));
        x11_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$1")));
        x11_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$2")));
        x11_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$0")));
        x11_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$1")));
        x11_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$2")));
        x11_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$0")));
        x11_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$1")));
        x11_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$2")));
        bounds.bound(x11, x11_upper);

        TupleSet x12_upper = factory.noneOf(3);
        x12_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$0")).product(factory.tuple("CatalogState$0")));
        x12_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$0")).product(factory.tuple("CatalogState$1")));
        x12_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$0")).product(factory.tuple("CatalogState$2")));
        x12_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$1")).product(factory.tuple("CatalogState$0")));
        x12_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$1")).product(factory.tuple("CatalogState$1")));
        x12_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$1")).product(factory.tuple("CatalogState$2")));
        x12_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$2")).product(factory.tuple("CatalogState$0")));
        x12_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$2")).product(factory.tuple("CatalogState$1")));
        x12_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$2")).product(factory.tuple("CatalogState$2")));
        x12_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$0")).product(factory.tuple("CatalogState$0")));
        x12_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$0")).product(factory.tuple("CatalogState$1")));
        x12_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$0")).product(factory.tuple("CatalogState$2")));
        x12_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$1")).product(factory.tuple("CatalogState$0")));
        x12_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$1")).product(factory.tuple("CatalogState$1")));
        x12_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$1")).product(factory.tuple("CatalogState$2")));
        x12_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$2")).product(factory.tuple("CatalogState$0")));
        x12_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$2")).product(factory.tuple("CatalogState$1")));
        x12_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$2")).product(factory.tuple("CatalogState$2")));
        x12_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$0")).product(factory.tuple("CatalogState$0")));
        x12_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$0")).product(factory.tuple("CatalogState$1")));
        x12_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$0")).product(factory.tuple("CatalogState$2")));
        x12_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$1")).product(factory.tuple("CatalogState$0")));
        x12_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$1")).product(factory.tuple("CatalogState$1")));
        x12_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$1")).product(factory.tuple("CatalogState$2")));
        x12_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$2")).product(factory.tuple("CatalogState$0")));
        x12_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$2")).product(factory.tuple("CatalogState$1")));
        x12_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$2")).product(factory.tuple("CatalogState$2")));
        bounds.bound(x12, x12_upper);

        TupleSet x13_upper = factory.noneOf(2);
        x13_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$0")));
        x13_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$1")));
        x13_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Catalog$2")));
        x13_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$0")));
        x13_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$1")));
        x13_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Catalog$2")));
        x13_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$0")));
        x13_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$1")));
        x13_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Catalog$2")));
        bounds.bound(x13, x13_upper);

        TupleSet x14_upper = factory.noneOf(2);
        x14_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Asset$0")));
        x14_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Asset$1")));
        x14_upper.add(factory.tuple("ApplicationState$0").product(factory.tuple("Asset$2")));
        x14_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Asset$0")));
        x14_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Asset$1")));
        x14_upper.add(factory.tuple("ApplicationState$1").product(factory.tuple("Asset$2")));
        x14_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Asset$0")));
        x14_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Asset$1")));
        x14_upper.add(factory.tuple("ApplicationState$2").product(factory.tuple("Asset$2")));
        bounds.bound(x14, x14_upper);

        TupleSet x15_upper = factory.noneOf(2);
        x15_upper.add(factory.tuple("CatalogState$0").product(factory.tuple("Asset$0")));
        x15_upper.add(factory.tuple("CatalogState$0").product(factory.tuple("Asset$1")));
        x15_upper.add(factory.tuple("CatalogState$0").product(factory.tuple("Asset$2")));
        x15_upper.add(factory.tuple("CatalogState$1").product(factory.tuple("Asset$0")));
        x15_upper.add(factory.tuple("CatalogState$1").product(factory.tuple("Asset$1")));
        x15_upper.add(factory.tuple("CatalogState$1").product(factory.tuple("Asset$2")));
        x15_upper.add(factory.tuple("CatalogState$2").product(factory.tuple("Asset$0")));
        x15_upper.add(factory.tuple("CatalogState$2").product(factory.tuple("Asset$1")));
        x15_upper.add(factory.tuple("CatalogState$2").product(factory.tuple("Asset$2")));
        bounds.bound(x15, x15_upper);

        TupleSet x16_upper = factory.noneOf(2);
        x16_upper.add(factory.tuple("CatalogState$0").product(factory.tuple("Asset$0")));
        x16_upper.add(factory.tuple("CatalogState$0").product(factory.tuple("Asset$1")));
        x16_upper.add(factory.tuple("CatalogState$0").product(factory.tuple("Asset$2")));
        x16_upper.add(factory.tuple("CatalogState$1").product(factory.tuple("Asset$0")));
        x16_upper.add(factory.tuple("CatalogState$1").product(factory.tuple("Asset$1")));
        x16_upper.add(factory.tuple("CatalogState$1").product(factory.tuple("Asset$2")));
        x16_upper.add(factory.tuple("CatalogState$2").product(factory.tuple("Asset$0")));
        x16_upper.add(factory.tuple("CatalogState$2").product(factory.tuple("Asset$1")));
        x16_upper.add(factory.tuple("CatalogState$2").product(factory.tuple("Asset$2")));
        bounds.bound(x16, x16_upper);

        TupleSet x17_upper = factory.noneOf(2);
        x17_upper.add(factory.tuple("CatalogState$0").product(factory.tuple("Asset$0")));
        x17_upper.add(factory.tuple("CatalogState$0").product(factory.tuple("Asset$1")));
        x17_upper.add(factory.tuple("CatalogState$0").product(factory.tuple("Asset$2")));
        x17_upper.add(factory.tuple("CatalogState$1").product(factory.tuple("Asset$0")));
        x17_upper.add(factory.tuple("CatalogState$1").product(factory.tuple("Asset$1")));
        x17_upper.add(factory.tuple("CatalogState$1").product(factory.tuple("Asset$2")));
        x17_upper.add(factory.tuple("CatalogState$2").product(factory.tuple("Asset$0")));
        x17_upper.add(factory.tuple("CatalogState$2").product(factory.tuple("Asset$1")));
        x17_upper.add(factory.tuple("CatalogState$2").product(factory.tuple("Asset$2")));
        bounds.bound(x17, x17_upper);

        TupleSet x18_upper = factory.noneOf(2);
        x18_upper.add(factory.tuple("CatalogState$0").product(factory.tuple("Asset$0")));
        x18_upper.add(factory.tuple("CatalogState$0").product(factory.tuple("Asset$1")));
        x18_upper.add(factory.tuple("CatalogState$0").product(factory.tuple("Asset$2")));
        x18_upper.add(factory.tuple("CatalogState$0").product(factory.tuple("Undefined$0")));
        x18_upper.add(factory.tuple("CatalogState$1").product(factory.tuple("Asset$0")));
        x18_upper.add(factory.tuple("CatalogState$1").product(factory.tuple("Asset$1")));
        x18_upper.add(factory.tuple("CatalogState$1").product(factory.tuple("Asset$2")));
        x18_upper.add(factory.tuple("CatalogState$1").product(factory.tuple("Undefined$0")));
        x18_upper.add(factory.tuple("CatalogState$2").product(factory.tuple("Asset$0")));
        x18_upper.add(factory.tuple("CatalogState$2").product(factory.tuple("Asset$1")));
        x18_upper.add(factory.tuple("CatalogState$2").product(factory.tuple("Asset$2")));
        x18_upper.add(factory.tuple("CatalogState$2").product(factory.tuple("Undefined$0")));
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

        Variable x22=Variable.unary("HidePreservesInv_this");
        Decls x21=x22.oneOf(x6);
        Expression x24=x22.join(x11);
        Formula x23=x24.in(x7);
        Formula x20=x23.forAll(x21);
        Expression x26=x11.join(Expression.UNIV);
        Formula x25=x26.in(x6);
        Variable x30=Variable.unary("HidePreservesInv_this");
        Decls x29=x30.oneOf(x6);
        Expression x34=x30.join(x12);
        Expression x36=x30.join(x11);
        Expression x35=x36.product(x9);
        Formula x33=x34.in(x35);
        Variable x39=Variable.unary("");
        Decls x38=x39.oneOf(x36);
        Expression x42=x39.join(x34);
        Formula x41=x42.one();
        Formula x43=x42.in(x9);
        Formula x40=x41.and(x43);
        Formula x37=x40.forAll(x38);
        Formula x32=x33.and(x37);
        Variable x46=Variable.unary("");
        Decls x45=x46.oneOf(x9);
        Expression x48=x34.join(x46);
        Expression x49=x30.join(x11);
        Formula x47=x48.in(x49);
        Formula x44=x47.forAll(x45);
        Formula x31=x32.and(x44);
        Formula x28=x31.forAll(x29);
        Expression x52=x12.join(Expression.UNIV);
        Expression x51=x52.join(Expression.UNIV);
        Formula x50=x51.in(x6);
        Variable x55=Variable.unary("HidePreservesInv_this");
        Decls x54=x55.oneOf(x6);
        Expression x58=x55.join(x13);
        Formula x57=x58.one();
        Expression x60=x55.join(x11);
        Formula x59=x58.in(x60);
        Formula x56=x57.and(x59);
        Formula x53=x56.forAll(x54);
        Expression x62=x13.join(Expression.UNIV);
        Formula x61=x62.in(x6);
        Variable x65=Variable.unary("HidePreservesInv_this");
        Decls x64=x65.oneOf(x6);
        Expression x67=x65.join(x14);
        Formula x66=x67.in(x8);
        Formula x63=x66.forAll(x64);
        Expression x69=x14.join(Expression.UNIV);
        Formula x68=x69.in(x6);
        Variable x72=Variable.unary("HidePreservesInv_this");
        Decls x71=x72.oneOf(x9);
        Expression x74=x72.join(x15);
        Formula x73=x74.in(x8);
        Formula x70=x73.forAll(x71);
        Expression x76=x15.join(Expression.UNIV);
        Formula x75=x76.in(x9);
        Variable x79=Variable.unary("HidePreservesInv_this");
        Decls x78=x79.oneOf(x9);
        Expression x81=x79.join(x16);
        Expression x82=x79.join(x15);
        Formula x80=x81.in(x82);
        Formula x77=x80.forAll(x78);
        Expression x84=x16.join(Expression.UNIV);
        Formula x83=x84.in(x9);
        Variable x87=Variable.unary("HidePreservesInv_this");
        Decls x86=x87.oneOf(x9);
        Expression x89=x87.join(x17);
        Expression x90=x87.join(x15);
        Formula x88=x89.in(x90);
        Formula x85=x88.forAll(x86);
        Expression x92=x17.join(Expression.UNIV);
        Formula x91=x92.in(x9);
        Expression x94=x16.intersection(x17);
        Formula x93=x94.no();
        Variable x97=Variable.unary("HidePreservesInv_this");
        Decls x96=x97.oneOf(x9);
        Expression x99=x97.join(x18);
        Expression x101=x97.join(x15);
        Expression x100=x101.union(x10);
        Formula x98=x99.in(x100);
        Formula x95=x98.forAll(x96);
        Expression x103=x18.join(Expression.UNIV);
        Formula x102=x103.in(x9);
        Variable x106=Variable.unary("HidePreservesInv_this");
        Decls x105=x106.oneOf(x9);
        Expression x109=x106.join(x16);
        Expression x110=x106.join(x17);
        Expression x108=x109.union(x110);
        Expression x111=x106.join(x15);
        Formula x107=x108.eq(x111);
        Formula x104=x107.forAll(x105);
        Variable x116=Variable.unary("HidePreservesInv_cs");
        Decls x115=x116.oneOf(x9);
        Variable x118=Variable.unary("HidePreservesInv_cs'");
        Decls x117=x118.oneOf(x9);
        Decls x114=x115.and(x117);
        Expression x124=x116.join(x18);
        Formula x123=x124.eq(x10);
        Expression x127=x116.join(x18);
        Formula x126=x127.some();
        Expression x129=x116.join(x18);
        Expression x130=x116.join(x17);
        Formula x128=x129.in(x130);
        Formula x125=x126.and(x128);
        Formula x122=x123.or(x125);
        Expression x135=x116.join(x18);
        Formula x134=x135.eq(x10);
        Formula x133=x134.not();
        Expression x138=x118.join(x16);
        Expression x140=x116.join(x16);
        Expression x141=x116.join(x18);
        Expression x139=x140.union(x141);
        Formula x137=x138.eq(x139);
        Expression x143=x118.join(x15);
        Expression x144=x116.join(x15);
        Formula x142=x143.eq(x144);
        Formula x136=x137.and(x142);
        Formula x132=x133.and(x136);
        Expression x146=x118.join(x18);
        Formula x145=x146.eq(x10);
        Formula x131=x132.and(x145);
        Formula x121=x122.and(x131);
        Formula x120=x121.not();
        Expression x149=x118.join(x18);
        Formula x148=x149.eq(x10);
        Expression x152=x118.join(x18);
        Formula x151=x152.some();
        Expression x154=x118.join(x18);
        Expression x155=x118.join(x17);
        Formula x153=x154.in(x155);
        Formula x150=x151.and(x153);
        Formula x147=x148.or(x150);
        Formula x119=x120.or(x147);
        Formula x113=x119.forAll(x114);
        Formula x112=x113.not();
        Formula x156=x0.eq(x0);
        Formula x157=x1.eq(x1);
        Formula x158=x2.eq(x2);
        Formula x159=x3.eq(x3);
        Formula x160=x4.eq(x4);
        Formula x161=x5.eq(x5);
        Formula x162=x6.eq(x6);
        Formula x163=x7.eq(x7);
        Formula x164=x8.eq(x8);
        Formula x165=x9.eq(x9);
        Formula x166=x10.eq(x10);
        Formula x167=x11.eq(x11);
        Formula x168=x12.eq(x12);
        Formula x169=x13.eq(x13);
        Formula x170=x14.eq(x14);
        Formula x171=x15.eq(x15);
        Formula x172=x16.eq(x16);
        Formula x173=x17.eq(x17);
        Formula x174=x18.eq(x18);
        Formula x19=Formula.compose(FormulaOperator.AND, x20, x25, x28, x50, x53, x61, x63, x68, x70, x75, x77, x83, x85, x91, x93, x95, x102, x104, x112, x156, x157, x158, x159, x160, x161, x162, x163, x164, x165, x166, x167, x168, x169, x170, x171, x172, x173, x174);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
       // solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);
        System.out.println("Solving...");
        System.out.flush();
        Solution sol = solver.solve(x19,bounds);
        System.out.println(sol.toString());
    }}