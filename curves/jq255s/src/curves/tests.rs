use crate::{Affine, Config, Projective};
use ark_ec::{AdditiveGroup, AffineRepr, CurveConfig};
use ark_ff::{vec, vec::Vec, Field};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;

/// The other representant of the identity (`N =(0 + N)`).
fn n() -> Projective {
    Projective {
        e: <Config as CurveConfig>::BaseField::ONE,
        z: <Config as CurveConfig>::BaseField::ONE,
        u: <Config as CurveConfig>::BaseField::ZERO,
        t: <Config as CurveConfig>::BaseField::ZERO,
    }
}

#[test]
fn decode_encode() {
    let mut rng = ark_std::test_rng();
    let a = Affine::rand(&mut rng);

    let mut compressed_bytes = Vec::new();
    a.serialize_compressed(&mut compressed_bytes).unwrap();

    let mut uncompressed_bytes = Vec::new();
    a.serialize_uncompressed(&mut uncompressed_bytes).unwrap();

    let a_compressed = Affine::deserialize_compressed(&*compressed_bytes).unwrap();
    let a_uncompressed = Affine::deserialize_uncompressed(&*uncompressed_bytes).unwrap();

    assert_eq!(a_compressed, a);
    assert_eq!(a_uncompressed, a);
}

/// These test vectors originate from Thomas Pornin's implementation of Jq255e and Jq255s:
/// <https://github.com/doubleodd/c-jq255> (Thomas Pornin, 2022)
/// The Arkworks framework's implementation of field element (de)serialization follows
/// the encoding specification of said paper, Appendix A.1.
#[test]
fn valid_decode() {
    let encoded_points: Vec<&str> = vec![
        "0000000000000000000000000000000000000000000000000000000000000000",
        "b1c26ad124f0b9b235e811fb02576bdeed7f6f2bdb9625ce867bbc2bbd751e59",
        "aef7d911554e0e1527f49d49d303e7da00532359589f1d56528005cbac70b153",
        "318b64b9ae83047670e6256054e6b5c0ffc3f9cb24659d809d946a7cf72a7521",
        "66a968dfe975050781f837e3ee6bf0352a969e53e4f66d1276b2c433568ea26b",
        "285611df1d4459f29fe7cbcbb98c752306d75664851836e50c347401a664f270",
        "851a83fabfc063883c88904475b53dce04d664f31e0fa678e297e3d2dee58732",
        "50ce42f8d53d0e1b79185c5be821578dd2a86b20084a6c0eff47b6431457ec64",
        "77859488c089928c355581d2a8e86154b94373ebcaaba991ad4ef19e4fb0352a",
        "bd9f4067b33ea224f281e8fb8b89c9317151796b415d7e491fb469c7289ed058",
        "3a89543388ce55e915cc870a4db2dd4fd9ad2e618f5a5013a45b67505859957e",
        "1bb1041d4123f462baf68ad3e6fc2aee7b2d30291ffd478379ead57470b1281a",
        "8d902970535a38b5e8d283a55d8cfe4ad62291916b000e561ec78e81d30f3160",
        "5758687972e24623a80af50fb524ecced34ade656a701644c764e30517a37713",
        "7f013fcabb9d8d29c2d44764703a4d69b1841db608bb1043e51d39dbd29f8739",
        "9afcc2b95049ee0feb5787056d301115e0b4d22b8ec82cdc4c37e80a7990b901",
        "d696e2470eb8a2a9c86a87791ee99852e4e51cb2be78e826e73fd73037df3a00",
        "510467bcd2af8b15e4833126e9ab0057c86e743420bf6681a664447f115d0118",
        "14ed9c64000ce1100827fa3ec256b7b09d0f3e009dbaccc17ad4e08d62172b37",
        "51fe4489d8c6f777feb613dd9cfc5160a12cc30c2e48bb1594e32bdbfa8a5f49",
        "dcc3f03e68c699d5be18958e90d9efad3ffec41de365807633592ff89d306771",
    ];
    for encoded_point in encoded_points.iter() {
        let point_serialized = hex::decode(encoded_point).unwrap();
        let point = Affine::deserialize_compressed(&*point_serialized).unwrap();

        let mut compressed_bytes = Vec::new();
        point.serialize_compressed(&mut compressed_bytes).unwrap();
        assert!(point_serialized == compressed_bytes);
    }
}

#[test]
fn valid_point_addition() {
    let encoded_points_vector: Vec<[&str; 6]> = vec![
        [
            "381c4e1998ea738fcee1d18779bebb36271ef55a5bcc3a5595717576e2ce704d",
            "db479deeb0d8e6096b33dd9dd4e18d385308cb553faa89ce8681df208860a110",
            "e0e467a709f40a935a8b1c5e78a745924a0eecc58576c99866b20e435fd7a821",
            "e02e26cc7657170f7e3ca5e9fd7fb11712928b55fb007df9d62f805c49be5673",
            "d60aacf148e642d5f31a4307300ffd46f6235dee653e7ea611484586669aee01",
            "03955a234b2760184666f43a9f3aa1b94330a37d4a2722cfc2dcf436fb67ad52",
        ],
        [
            "60f36f052234d98450e0131f5cea458af31b5e36df99c7ac77e8febfd6bd4562",
            "eec699499ef822479c929686a6fcfb68bd7c03004af40a6e7120e61bf946ff0f",
            "011e0b7c6a3332b8d81a44cb34a4a6e5428d1a1e2f0b68973f65331a2aa37421",
            "075b9051e80d2d25c8f289331e5abda12a9046c8269994fbbcd0408f8196805d",
            "a5d16235f08f5db6c03138c280e7b79fdf3abb1f5c9cbbaebbac00d7b5e58d15",
            "90a2dd8393d8f80f07b323a6a3f71aca392ee9355a285d3a924c0a08fdcdb12f",
        ],
        [
            "5f999a844a1142c521b30d7962c5d1cc51f44b73310f2859fba957bbde789250",
            "0e463bcd3d7a94dbe0c1db26bb8a1ceaa02f3bb5a158690959aae534a99d5753",
            "8532065bd0f3442f01b315eb0088f42656959eb082e6ff5064e7739383a1e50a",
            "44d0ee20649420c8514f2b152e8551334df9755f18eed00225c0ea4aaff52262",
            "5e026732df7af8d6265a9021cbccd6b4653353171fe228ab3c3a26911a72b421",
            "b0e8da551c65613e0f8e90bbb987941b55eb1818f9c4747cfeba1f6bd715e139",
        ],
        [
            "3ea95fbb3baca80e0340315c688ec8b898b17a491f452e2a2e7d7b7d948d2171",
            "2cc136fb22b80d783f6a8162b1292fc9192cd5be4d719c52cff60e6cdd845119",
            "dda4bf35cd7d5c05e49b37640df81a385e4cd9e540e6a84782a57f53543e3b2d",
            "c11fe3be926b10336cbb8f191e31459c6fa492629c773f5d7214536cd299a367",
            "3ba12da38f381c060ac30c20adb436cb816b01fcf72ab777cbae7525767ec044",
            "61987cfeb7e4c45f742d1d6efd5d04b7d7a10246e591d947791d64da569c2d6e",
        ],
        [
            "6c44d7a7569c28f80b12273d5ad2308f1241eb1e42d0b92a67213b7e908ad14d",
            "e9b5567f03125c2357ad2190a852c3dec98dfd919721f385066b28f797c64e6c",
            "acedfb558a43ef11ece45956d15a4ce8e206f101311ef7ae51d89fdf1d593304",
            "5974f71abe178125b92b559ee5025e004c37b29e570e1b05702bac49160b221e",
            "9814abe67e6f98b67c7abb8f192d9177b5b707f3e0eec52a08442f3bb6e80464",
            "9e6725094371bfe29b6e114b29bf12eff0167b93b98b611734cdd3e196a0f52f",
        ],
        [
            "bee7f22a49b9e5404162552437d11fff2b773b4111ada2ec8dc0faab67243261",
            "c7c2c162ba7a3c0b8ed64176b959207e396b43b9eb5429c418528bfc1370331a",
            "f0615e44ab681f5f6823b3b441a39fb5f518ba448eacce1f104008771e33fb29",
            "95e9fd29ea0c0bacabc1d4158503890784c3c37f3b35c70c9ae45d94caf58329",
            "02c5f804b8607d5525e52810a3d000cd489fe7b79109239b26af3d9d4085d658",
            "95faa802ad86ba6929fc3b01730daa232076aef3b063ebb6b309cfea61f9e741",
        ],
        [
            "19ea6d24f1511a233c198ed0895d3fc76161a3e48f310b15cc8e6730cc2c1026",
            "5755e6da5c23c5f0c67b9b1c7f7e8b02aea0ac07498d206b5efa045489e1d737",
            "096ab36803970aa88bf6000f889267543299016c63ea2c629df4e9ed985d862d",
            "8ad8630a4117f64a7d78deded3400ea6adf8f92f98ddfc85c1b1b5819b5d4046",
            "8cbc2d5148c3c78acca57399073370089f535da059a93415788a1528469eea4a",
            "6bbb60d1fc041b826313dc3c0a5116e71767e252cee93c8dc512516979b4ea12",
        ],
        [
            "88b303961b1ada474b2294750bd00f1c935f0e6f1de20b07c4e971fb67527f51",
            "823978efdd5b7b305262287900a4eb96cf5e61c351a13a9e3bd61efa687a5866",
            "dd5c8e2ede2ad115a1edcc72c2e3c264e300fce3a4e3d0f09f504e023ac9e31e",
            "20049f4a29799b829533ffe67cbf70279b88bb19a6ffe62b670914b5bafae025",
            "1b7ade87df630960d5295480937545974949714c66184ad3770542f7377e2301",
            "ea9fd3440c0a193d56e93589541d55f25bafcda89d66986689ee171823951666",
        ],
        [
            "add5c3e78cb10a1f9ba69997804838250506cc7678649b483e6299e045497371",
            "7483ee768a54e1f3b19422c9bdab65ed8c0688483cf8fc3f80a08d07bcac0622",
            "c9b187ab32b93e9acbd2600d79985eb6e1b0daaea7dee8a372955bf36beba27b",
            "8ae1eecc6db1a3866c2ace308989a0f8ddbfb9b182da844aadc05148aca0e25b",
            "4c8e8c39fe3370d9fa1797dacc26aa93463bbb2cf8309140c43bcb0e16842e39",
            "92082e52bdd0091846e0be899144cc553379b723f609947ff95c6308b3e55a25",
        ],
        [
            "00219fcb3c4a5cfb84c0cfb2e0be0c2fc0dc50be01bd15c0849cd2b4e86a8753",
            "61cba11b9c106484a8d3b677fd42ea9aed3c4e3211cf87845db59d085406385b",
            "5c32d46832a9e72ba1b334176d5afb4b499915479559c99ac900abde03d3a503",
            "599f2e7e822c06eeeb98477975b18664556c9de5070e296bb547a5d6b064d153",
            "4b9d81c62c6b1ed1159db5a6b4af8161b7ec864740bc2bb3e49627997043bb0a",
            "4cd2ca03930823ea167e6cdc738cf4bba68960999d26ef6b748ba8ac1fb9f61c",
        ],
        [
            "f881d61f1d74ec291e82eb12b274789ceb22541a1d62f58f26c946aa8262954f",
            "a26b9edd4f33a8d27ec17b0834ab1631198bc7a86d34f22eb88b5b59dee40a5b",
            "9bc3688ede79d6d6fcb5f29576e8f4fe00a47ab49913b3ee3a66ec5c901e4137",
            "716f532220d997612022d61df0f2aa890dc087039ddbe6fa315d89e58ffadd72",
            "1c209ccdc7fc984d4d03b763cdfdf0e5ce81d22eeb710057e80b49f2fe7bf74d",
            "8067c4ac59dc0f95470c06efa63820c3ed714146167216eff0ba61fd0ab12c04",
        ],
        [
            "6d06d460392a61e9011d18622610ad4ae2b40352a787c440e458bd67e81bac6c",
            "acbe4ea45fb6c601d0b0da1346ddc2315e851def7555c90ef460f9088cd7114b",
            "ed3af00b64e16034cdcd3b5344ca4bcb686f61af5894f685f353b06140b8ef75",
            "d4cff64435af65e2d73db04984c9b1724614827ad272ebb9fc76646885bf5328",
            "2309d522f92b184f7c290a71823f79b9f0c72020c5b6554b4647f813da77ff3d",
            "2f910bd99152d1b56542fd3965ede38ba9647516dddcc1a5bc9db0aa645b8103",
        ],
        [
            "94fed56d5124d271fd3b63cd17f4f3bd6f3fb9c9b3a2f2dee7abacfada3ab969",
            "25debeac62ccaf5c8d5019580c7ef97e78c769ca6514e6873e9622cb74b18171",
            "7413d872bb58181d56d0e288d2993b2a552845292632b45bceb2fd8f3a4ef614",
            "fd3526dc4a70604ac9986f916129cfb5995b8aac2093dd06c338cfebcd23062d",
            "8ded66b6e0bfa56a27a5fa4e763545064849e35ee855d65f73546832f9dc0d54",
            "835d25ab5b57ed33402ab7c6701755117619948a558878193fecee12cd6bb150",
        ],
        [
            "780fc3cd9224249d1df0ff142f552629846bb1f1beba2621bf79f85a9d314d56",
            "3175dac57c3a693980287572a2c14d0a59a4f078af8d00a79b38ec982b25730d",
            "da270fc356d1a119132b75504682dd56ccbac891d100e8c794d0833285c1c34f",
            "abe881a298959bac0e8ab0b111348a31c3c3c9dada2ccae15a853685f9ac2b46",
            "bb1344014186f4219716a740867b0e7dfc3297de7b35240ec0cfcccb383be57f",
            "9e0bbb128e78780dfa725cd8934e025097be87672f24b5733b41f5f23a5a3549",
        ],
        [
            "eed74e9cbd63ddb8f3ca345ebab1b0ba9cc6bd53ec6096fc059354319957fa74",
            "f921125ccf44d17ce2d8d0f29a9f59e0f73d8a759ac8f7ef9250f4d5fb0d7426",
            "1f36c8e821941eb90d24c6341e75d94aeeb2527863a6a634fca5d38f42663430",
            "7e82ad365a5f308390a0ebfd73952cf924050f03620a1e0fec69797a2179235d",
            "aca89dc458bd0e2ca0f73c09e495b2241c085011ab786f707d8c3c1c2f7ebc4a",
            "5c52e4759076e2558be0b5ade6e1bd53c99514c656d61ae4dadbcd63b0934a30",
        ],
        [
            "97dc9ac2154cc71d4bb42fb46afb064924e538a88db86d52397cebe124b4b075",
            "3ccc7026466bae54512a3f4ff7f85e703872b74f517a4b607dd5be5a8412a16d",
            "2ddfb977bb7fdc7880efed6953ee1604de69df616964f8a127437e0e98dba361",
            "7185bd0d698a74852ac7639fc9b955bc722f30a019170f01644a353c24e8cd2f",
            "47229988a81941e122554b34bf81e2a75bbacaf44bf263c716cb2725665aa37b",
            "414b57d106ac19110db4815c8e59be5c47af99b139e8ccf13025c39be320195e",
        ],
        [
            "fca688816addd850c8930696a49a1e6fb9e14255b03aa86dddd049f6cce8ee67",
            "53f9d223569e492d78fd4b6665ae8994c6a1f852a6c38a60072a87240062d808",
            "706ba0b5f5ce767b83fa2c539e4daaa750e5bd43c95acd5a1eac3d4afd6d6508",
            "9a26cbf9ea28d031068bcf81b642aa9044f0fda980766d22a6b2c8e479b30840",
            "18a65ad2f85cd3c3f2fdb6fd4a4d88e523ec93b19894ffce6f3fb931740d1607",
            "36522522608857cd94e8dd9814bed64f12bf8a6845098b284457376544afd820",
        ],
        [
            "293907dbcfab4d4dab6b9edc338997da0d107f3cb47f3531e75c04d23171ee6f",
            "e35d3b0cea71bdfa31be71d19eb58c7a86a4566169f17980d2b32a95b9f3ee54",
            "2f78f90f07e8d242bed8fd5a160fdeda7924d045b77b228ae7d2b9a46e1b1e07",
            "68564e3f97a87ee54e66bdd31f98efd95f90c0081bb348dd179ed547d4732c55",
            "5005f9700eed61c2e68e37bb0607d4236ada34c602ed86e0160b0146a9e1b339",
            "595fe35df7e10174845e5ce6f334f7be092a82b56bdaccbbf19bb5b11d33d171",
        ],
        [
            "78cb0a784a503a4386928f22754e772223587faf2cc8950dd6e386680a86ba65",
            "a4b5c97f1972b54c13d7b050666d6d198ad63e21a9c06e965025ca7e44e9f000",
            "5764e56b2d8896fedf97c30fc2a9d5ad5c2900a0389dd6234c55f166a036ad18",
            "500269aaa0bfe99b6f16a1cd2dd1b21668c5e085b1782de1307449732009cd1b",
            "b936238a475ae0851b89b4c63e094791ac6a03846afad8c7300c77a456bd6e58",
            "6a7690687763248b89a41ac65607a3a88c539a7cfdd3079102b33b2ea607506b",
        ],
        [
            "c671c46c3f35165106b26b49873a17a202004883c5a56962d5a13fc4dbcaec44",
            "a04f9846c83204d54f26bab44530c83b4aaa5dfa7772084fcc30a1ab1a9bff1c",
            "552db8f5fad91c4b2d81a021e0e5ef3683c279d8ffa40097417e2fb483c3e23c",
            "aeb8c01dd8a194abb8a6a34c482627e8acbb3b64c8b5470edb9ebddfadc4c61a",
            "8e57d5813af955b94447161bb9965da513f4595e6dc961767cb123657aa1bd50",
            "5b5a5a734813bd45fc5c08015eaca263fa715584b15409730a64b4c20123af7a",
        ],
    ];
    for encoded_points in encoded_points_vector.iter() {
        let p1 =
            Affine::deserialize_compressed_unchecked(&*hex::decode(encoded_points[0]).unwrap())
                .unwrap();
        let p2 =
            Affine::deserialize_compressed_unchecked(&*hex::decode(encoded_points[1]).unwrap())
                .unwrap();

        let p1_p2 = p1 + (p2 + n());
        let p3 =
            Affine::deserialize_compressed_unchecked(&*hex::decode(encoded_points[2]).unwrap())
                .unwrap()
                .into_group();
        assert!(p1_p2 == (p3 + n()));

        let p1_p1 = p1 + p1;
        let p4 =
            Affine::deserialize_compressed_unchecked(&*hex::decode(encoded_points[3]).unwrap())
                .unwrap()
                .into_group();
        assert!(p1_p1 == p4);

        let p1_p1_p2 = p1 + p1 + p2;
        let p5 =
            Affine::deserialize_compressed_unchecked(&*hex::decode(encoded_points[4]).unwrap())
                .unwrap()
                .into_group();
        assert!(p1_p1_p2 == p5);

        let p1_p1_p2_p2 = p1 + p1 + p2 + p2;
        let p6 =
            Affine::deserialize_compressed_unchecked(&*hex::decode(encoded_points[5]).unwrap())
                .unwrap()
                .into_group();
        assert!(p1_p1_p2_p2 == p6);
    }
}

fn bytes_to_bigint(bytes: Vec<u8>) -> ark_ff::BigInteger256 {
    let mut arr: [u64; 4] = [0, 0, 0, 0];
    for i in 0..4 {
        arr[i] = ((bytes[0 + (i * 8)] as u64) << 0)
            + ((bytes[1 + (i * 8)] as u64) << 8)
            + ((bytes[2 + (i * 8)] as u64) << 16)
            + ((bytes[3 + (i * 8)] as u64) << 24)
            + ((bytes[4 + (i * 8)] as u64) << 32)
            + ((bytes[5 + (i * 8)] as u64) << 40)
            + ((bytes[6 + (i * 8)] as u64) << 48)
            + ((bytes[7 + (i * 8)] as u64) << 56)
    }
    ark_ff::BigInt::new(arr)
}

#[test]
fn valid_scalar_multiplication() {
    let encoded_points_and_scalars_vec: Vec<[&str; 3]> = vec![
        [
            "5d10110ee82efbc1a71e2368d4adc4ebb019500b26cb643301397f6e6dd7c41c",
            "5a1dd472a60feb189f0390fc83f771847248b7d198a9864e3402cbbf743f7b04",
            "713806b513462b8abbbae0b5adee4f39895b6886e26b6214125502a233f92e17",
        ],
        [
            "dcc05a8fa09832a6b63f6f02ebf7d682952b53da2f199ca7ebb8717da81c9f43",
            "de9e8923f07ac1aa7582b4a4c4b4988621f7a5f0aec01f7cb72cf3b089d37d2a",
            "a80183ba294a31c8a42cb6bc48829ebeb53c3279da3990d3597e4fb225472238",
        ],
        [
            "fd4b6116d3f096fa2922c9e350322558c371ed67c1d1ddccf82918bc9f0db34e",
            "4a461514ff2738927d0138f53123bb9111fa46520c4c83347ad672e72d94be0e",
            "5f0d63130bc98a59dbb7d537ff42c923866f51b529ade1978811ed1f91c8cd60",
        ],
        [
            "5367b651b5bc251a732b1314cfff3349187db32563e08516f663950485263d6b",
            "b6c0c6f08e666c9d74a5592f1d47cdf3757549139cbdd4d3ff9c2d2651d68b34",
            "5d73e39320332aaddd578b61c2724d6edd09e4e8e41ca6bfe23dbc796a79f07e",
        ],
        [
            "e19574765ff50b7a051b58492b1b1d2ee79b77e3ae9adc4a7be3c1c2c2cbd611",
            "b18f05606bc26ec86adaa37467ec53a87219f2013c45369e8104efaf6766cd13",
            "4eaf39f207d63efbf6346dd326d58c8caba08297037674dc5883d04bbe94d969",
        ],
        [
            "f1a2cbfe94aa32dd9124d88ccc6077441ab119770618642a9414389014ae5a52",
            "678753e1d1de60d2f3622d949e686a7560809737bd806c2fce29bd16c6c11117",
            "9c36fc160d3cfb33508f16ae0e3c746c16640ee9686193d3cfa1581cd55f0243",
        ],
    ];

    for encoded in encoded_points_and_scalars_vec.iter() {
        let p = Affine::deserialize_compressed_unchecked(&*hex::decode(encoded[0]).unwrap())
            .unwrap()
            .into_group();
        let n = crate::Fr::from(bytes_to_bigint(hex::decode(encoded[1]).unwrap()));
        let pn = p * n;
        let p2 = Affine::deserialize_compressed_unchecked(&*hex::decode(encoded[2]).unwrap())
            .unwrap()
            .into_group();
        assert!(pn == p2)
    }
}
