#[derive(
    Default, Debug, Clone, PartialEq, Eq, serde_derive::Serialize, serde_derive::Deserialize,
)]
#[serde(rename_all = "camelCase")]
pub struct SuiteVector {
    pub ciphersuite: String,
    pub curve: String,
    pub dst: String,
    pub field: Field,
    pub hash: String,
    pub map: Map,
    pub random_oracle: bool,
    pub vectors: Vec<Vector>,
}

#[derive(
    Default, Debug, Clone, PartialEq, Eq, serde_derive::Serialize, serde_derive::Deserialize,
)]
#[serde(rename_all = "camelCase")]
pub struct Field {
    pub m: String,
    pub p: String,
}

#[derive(
    Default, Debug, Clone, PartialEq, Eq, serde_derive::Serialize, serde_derive::Deserialize,
)]
#[serde(rename_all = "camelCase")]
pub struct Map {
    pub name: String,
}

#[derive(
    Default, Debug, Clone, PartialEq, Eq, serde_derive::Serialize, serde_derive::Deserialize,
)]
#[serde(rename_all = "camelCase")]
pub struct Vector {
    #[serde(rename = "P")]
    pub p: P,
    pub msg: String,
    pub u: Vec<String>,
}

#[derive(
    Default, Debug, Clone, PartialEq, Eq, serde_derive::Serialize, serde_derive::Deserialize,
)]
#[serde(rename_all = "camelCase")]
pub struct P {
    pub x: String,
    pub y: String,
}
