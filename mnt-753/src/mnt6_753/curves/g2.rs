use ark_ff::{
    biginteger::BigInteger768,
    field_new,
};
use ark_ec::{
    mnt6,
    mnt6::MNT6Parameters,
    models::{ModelParameters, SWModelParameters},
};

use crate::mnt6_753::{self, g1, Fq, Fq3, Fr, FQ_ZERO};

pub type G2Affine = mnt6::G2Affine<mnt6_753::Parameters>;
pub type G2Projective = mnt6::G2Projective<mnt6_753::Parameters>;
pub type G2Prepared = mnt6::G2Prepared<mnt6_753::Parameters>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Parameters;

impl ModelParameters for Parameters {
    type BaseField = Fq3;
    type ScalarField = Fr;
}

/// MUL_BY_A_C0 = NONRESIDUE * COEFF_A
#[rustfmt::skip]
pub const MUL_BY_A_C0: Fq = field_new!(Fq, BigInteger768([
    10895242587870565906,
    6757387713923212228,
    12683949709867392876,
    1229095484098138811,
    18111217745394181988,
    3648021353977015866,
    7900332254549424237,
    5988529219097278134,
    11544487525720487778,
    7317517692149492894,
    9905728181042915773,
    470678396104534
]));

/// MUL_BY_A_C1 = NONRESIDUE * COEFF_A
#[rustfmt::skip]
pub const MUL_BY_A_C1: Fq = field_new!(Fq, BigInteger768([
    10895242587870565906,
    6757387713923212228,
    12683949709867392876,
    1229095484098138811,
    18111217745394181988,
    3648021353977015866,
    7900332254549424237,
    5988529219097278134,
    11544487525720487778,
    7317517692149492894,
    9905728181042915773,
    470678396104534
]));

/// MUL_BY_A_C2 = COEFF_A
pub const MUL_BY_A_C2: Fq = g1::Parameters::COEFF_A;

impl SWModelParameters for Parameters {
    const COEFF_A: Fq3 = mnt6_753::Parameters::TWIST_COEFF_A;
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
    #[rustfmt::skip]
    const COEFF_B: Fq3 = field_new!(
        Fq3,
        field_new!(Fq, BigInteger768([
                3284231658830416104,
                13720030246451177991,
                6276939417009443243,
                8340612253649729185,
                4863511590806861670,
                15883218135158530927,
                4865336109262680856,
                16600307443495218926,
                10112528487499131659,
                17308657107605697754,
                5326857497786417651,
                206191604157846
        ])),
        FQ_ZERO,
        FQ_ZERO,
    );

    /// COFACTOR =
    /// 1755483545388786116744270475466687259186947712032004459714210070280389500116987496124098574823389466285978151140155508638765729019174599527183600372094760023144398285325863550664578643924584541949466179502227232245309952839189635010671372908411609248348904807785904229403747495114436660255866932060472369629692502198423138429922875792635236729929780298333055698257230963645509826963717287902205842627121011526048163097042046361575549171961352924692480000
    #[rustfmt::skip]
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
    #[rustfmt::skip]
    const COFACTOR_INV: Fr = field_new!(Fr, BigInteger768([
            9418103049026957703,
            3464743017686961509,
            7872172759259099794,
            17514322419398292337,
            1496353716802911167,
            16961719271566193274,
            15426671498718617736,
            9230857178223113223,
            11731938389074297274,
            16450973680014766981,
            431917267220694852,
            94637508603012
    ]));

    /// AFFINE_GENERATOR_COEFFS = (G2_GENERATOR_X, G2_GENERATOR_Y)
    const AFFINE_GENERATOR_COEFFS: (Self::BaseField, Self::BaseField) =
        (G2_GENERATOR_X, G2_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(elt: &Fq3) -> Fq3 {
        field_new!(
            Fq3,
            MUL_BY_A_C0 * &elt.c1,
            MUL_BY_A_C1 * &elt.c2,
            MUL_BY_A_C2 * &elt.c0,
        )
    }
}

const G2_GENERATOR_X: Fq3 =
    field_new!(Fq3, G2_GENERATOR_X_C0, G2_GENERATOR_X_C1, G2_GENERATOR_X_C2);
const G2_GENERATOR_Y: Fq3 =
    field_new!(Fq3, G2_GENERATOR_Y_C0, G2_GENERATOR_Y_C1, G2_GENERATOR_Y_C2);

// Generator of G2
// These are three Fq elements each because X and Y (and Z) are elements of Fq^3
// X = 27250797394340459586637772414334383652934225310678303542554641987990991970766156209996739240400887081904395745019996048910447071686918567661896491214767494514394154061111870331668445455228882471000120574964265209669155206168252,
// 35762481056967998715733586393399457882827322353696313323665483142561285210083843314423554450886956650265947502285422529615273790981238406393402603210224104850580302463396274854098657541573494421834514772635884262388058080180368,
// 36955296703808958167583270646821654948157955258947892285629161090141878438357164213613114995903637211606408001037026832604054121847388692538440756596264746452765613740820430501353237866984394057660379098674983614861254438847846,
// Y = 2540920530670785421282147216459500299597350984927286541981768941513322907384197363939300669100157141915897390694710534916701460991329498878429407641200901974650893207493883271892985923686300670742888673128384350189165542294615,
// 7768974215205248225654340523113146529854477025417883273460270519532499370133542215655437897583245920162220909271982265882784840026754554720358946490360213245668334549692889019612343620295335698052097726325099648573158597797497,
// 21014872727619291834131369222699267167761185012487859171850226473555446863681002782100371394603357586906967186931035615146288030444598977758226767063525819170917389755555854704165900869058188909090444447822088242504281789869689,
#[rustfmt::skip]
pub const G2_GENERATOR_X_C0: Fq = field_new!(Fq, BigInteger768([
    12772807549130126376,
    2873211972983293592,
    15999100872160401842,
    5277158980096688998,
    12258756012310206056,
    11885883517271414939,
    6373672746025419911,
    13662747456330091710,
    11960680427306056040,
    15150766304321120168,
    9480712498131729809,
    413066879180657
]));

#[rustfmt::skip]
pub const G2_GENERATOR_X_C1: Fq = field_new!(Fq, BigInteger768([
    10478274013728260378,
    15392361149861123784,
    17610084573134912261,
    14474130264887792371,
    16754378329454263996,
    3186303078832273968,
    7143189323629797683,
    897486443141339765,
    3675579496642106405,
    4429391539758461550,
    18414257413872084180,
    331209511183940
]));

#[rustfmt::skip]
pub const G2_GENERATOR_X_C2: Fq = field_new!(Fq, BigInteger768([
    5133712986240959624,
    10763134357204872827,
    8672341403101541980,
    18084133226637702602,
    4689040548070804594,
    7352115990101270007,
    14358820512747653623,
    10167201669589504005,
    3117673189936726036,
    9407838052466059644,
    7246385421116647671,
    464288782946273
]));

#[rustfmt::skip]
pub const G2_GENERATOR_Y_C0: Fq = field_new!(Fq, BigInteger768([
    710862246533630948,
    9314168172257972041,
    4722111556929662508,
    4408676313209842703,
    10491088158750500898,
    13211840969745661306,
    13985341743807087374,
    7111198859398088665,
    158194789363472891,
    7682183069894584797,
    9510326135325230913,
    338826428359581
]));

#[rustfmt::skip]
pub const G2_GENERATOR_Y_C1: Fq = field_new!(Fq, BigInteger768([
    10889422482835557076,
    6073207585023077555,
    16059368148547235058,
    14871121891082823821,
    15156344465408677175,
    12695157488434086405,
    7840105431702704631,
    4763759818130023465,
    12295696339556388640,
    352741974984397506,
    10581333776569094279,
    204002329498100
]));

#[rustfmt::skip]
pub const G2_GENERATOR_Y_C2: Fq = field_new!(Fq, BigInteger768([
    11263496889641203707,
    16306762242042931049,
    8275973312257833978,
    12034012818098316014,
    5392903691498465561,
    4572635011530974247,
    696221667645211601,
    11098678912660456319,
    5477755854538915619,
    11442390115310629698,
    10262065045802790037,
    17901561410539
]));
