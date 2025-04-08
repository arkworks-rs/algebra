use ark_ec::{
    mnt6,
    mnt6::MNT6Config,
    models::{short_weierstrass::SWCurveConfig, CurveConfig},
};
use ark_ff::{AdditiveGroup, MontFp};

use crate::{g1, Fq, Fq3, Fr};

pub type G2Affine = mnt6::G2Affine<crate::Config>;
pub type G2Projective = mnt6::G2Projective<crate::Config>;
pub type G2Prepared = mnt6::G2Prepared<crate::Config>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
    type BaseField = Fq3;
    type ScalarField = Fr;

    /// COFACTOR =
    /// 1755483545388786116744270475466687259186947712032004459714210070280389500116987496124098574823389466285978151140155508638765729019174599527183600372094760023144398285325863550664578643924584541949466179502227232245309952839189635010671372908411609248348904807785904229403747495114436660255866932060472369629692502198423138429922875792635236729929780298333055698257230963645509826963717287902205842627121011526048163097042046361575549171961352924692480000
    const COFACTOR: &'static [u64] = &[
        17839255819456086016,
        500623104730997740,
        2110252009236161768,
        1500878543414750896,
        12839751506594314239,
        8978537329634833065,
        13830010955957826199,
        7626514311663165506,
        14876243211944528805,
        2316601947950921451,
        2601177562497904269,
        18300670698693155036,
        17321427554953155530,
        12586270719596716948,
        807965545138267130,
        13086323046094411844,
        16597411233431396880,
        5578519820383338987,
        16478065054289650824,
        12110148809888520863,
        5901144846689643164,
        3407195776166256068,
        14663852814447346059,
        13435169368,
    ];

    /// COFACTOR^(-1) mod r =
    /// 6983081827986492233724035798540106188028451653325658178630583820170892135428517795509815627298389820236345161981341515817589065927929152555581161598204976128690232061758269440757592419606754539638220064054062394397574161203200
    const COFACTOR_INV: Fr = MontFp!("6983081827986492233724035798540106188028451653325658178630583820170892135428517795509815627298389820236345161981341515817589065927929152555581161598204976128690232061758269440757592419606754539638220064054062394397574161203200");
}

/// MUL_BY_A_C0 = NONRESIDUE * COEFF_A
///             = 11 * 11
///             = 121
pub const MUL_BY_A_C0: Fq = MontFp!("121");

/// MUL_BY_A_C1 = NONRESIDUE * COEFF_A
///             = 11 * 11
///             = 121
pub const MUL_BY_A_C1: Fq = MontFp!("121");

/// MUL_BY_A_C2 = COEFF_A
pub const MUL_BY_A_C2: Fq = g1::Config::COEFF_A;

impl SWCurveConfig for Config {
    const COEFF_A: Fq3 = crate::Config::TWIST_COEFF_A;
    // B coefficient of MNT6-753 G2 =
    // ```
    // mnt6753_twist_coeff_b = mnt6753_Fq3(mnt6753_G1::coeff_b * mnt6753_Fq3::non_residue,
    //                                  mnt6753_Fq::zero(), mnt6753_Fq::zero());
    // non_residue = mnt6753_Fq3::non_residue = mnt6753_Fq("11");
    //  = (G1_B_COEFF * NON_RESIDUE, ZERO, ZERO);
    //  =
    //  (2189526091197672465268098090392210500740714959757583916377481826443393499947557697773546040576162515434508768057245887856591913752342600919117433675080691499697020523783784738694360040853591723916201150207746019687604267190251,
    //  0, 0)
    // ```
    const COEFF_B: Fq3 = Fq3::new(
        MontFp!("2189526091197672465268098090392210500740714959757583916377481826443393499947557697773546040576162515434508768057245887856591913752342600919117433675080691499697020523783784738694360040853591723916201150207746019687604267190251"),
        Fq::ZERO,
        Fq::ZERO,
    );

    /// AFFINE_GENERATOR_COEFFS = (G2_GENERATOR_X, G2_GENERATOR_Y)
    const GENERATOR: G2Affine = G2Affine::new_unchecked(G2_GENERATOR_X, G2_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(elt: Fq3) -> Fq3 {
        Fq3::new(
            MUL_BY_A_C0 * &elt.c1,
            MUL_BY_A_C1 * &elt.c2,
            MUL_BY_A_C2 * &elt.c0,
        )
    }
}

const G2_GENERATOR_X: Fq3 = Fq3::new(G2_GENERATOR_X_C0, G2_GENERATOR_X_C1, G2_GENERATOR_X_C2);
const G2_GENERATOR_Y: Fq3 = Fq3::new(G2_GENERATOR_Y_C0, G2_GENERATOR_Y_C1, G2_GENERATOR_Y_C2);

// Generator of G2
// These are three Fq elements each because X and Y (and Z) are elements of Fq^3
// X = 27250797394340459586637772414334383652934225310678303542554641987990991970766156209996739240400887081904395745019996048910447071686918567661896491214767494514394154061111870331668445455228882471000120574964265209669155206168252,
// 35762481056967998715733586393399457882827322353696313323665483142561285210083843314423554450886956650265947502285422529615273790981238406393402603210224104850580302463396274854098657541573494421834514772635884262388058080180368,
// 36955296703808958167583270646821654948157955258947892285629161090141878438357164213613114995903637211606408001037026832604054121847388692538440756596264746452765613740820430501353237866984394057660379098674983614861254438847846,
// Y = 2540920530670785421282147216459500299597350984927286541981768941513322907384197363939300669100157141915897390694710534916701460991329498878429407641200901974650893207493883271892985923686300670742888673128384350189165542294615,
// 7768974215205248225654340523113146529854477025417883273460270519532499370133542215655437897583245920162220909271982265882784840026754554720358946490360213245668334549692889019612343620295335698052097726325099648573158597797497,
// 21014872727619291834131369222699267167761185012487859171850226473555446863681002782100371394603357586906967186931035615146288030444598977758226767063525819170917389755555854704165900869058188909090444447822088242504281789869689,
pub const G2_GENERATOR_X_C0: Fq = MontFp!("27250797394340459586637772414334383652934225310678303542554641987990991970766156209996739240400887081904395745019996048910447071686918567661896491214767494514394154061111870331668445455228882471000120574964265209669155206168252");
pub const G2_GENERATOR_X_C1: Fq = MontFp!("35762481056967998715733586393399457882827322353696313323665483142561285210083843314423554450886956650265947502285422529615273790981238406393402603210224104850580302463396274854098657541573494421834514772635884262388058080180368");
pub const G2_GENERATOR_X_C2: Fq = MontFp!("36955296703808958167583270646821654948157955258947892285629161090141878438357164213613114995903637211606408001037026832604054121847388692538440756596264746452765613740820430501353237866984394057660379098674983614861254438847846");

pub const G2_GENERATOR_Y_C0: Fq = MontFp!("2540920530670785421282147216459500299597350984927286541981768941513322907384197363939300669100157141915897390694710534916701460991329498878429407641200901974650893207493883271892985923686300670742888673128384350189165542294615");
pub const G2_GENERATOR_Y_C1: Fq = MontFp!("7768974215205248225654340523113146529854477025417883273460270519532499370133542215655437897583245920162220909271982265882784840026754554720358946490360213245668334549692889019612343620295335698052097726325099648573158597797497");
pub const G2_GENERATOR_Y_C2: Fq = MontFp!("21014872727619291834131369222699267167761185012487859171850226473555446863681002782100371394603357586906967186931035615146288030444598977758226767063525819170917389755555854704165900869058188909090444447822088242504281789869689");
