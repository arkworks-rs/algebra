use crate::curves::{
    models::{SWModelParameters, TEModelParameters},
    short_weierstrass_jacobian::{GroupAffine as SWAffine, GroupProjective as SWProjective},
    twisted_edwards_extended::{GroupAffine as TEAffine, GroupProjective as TEProjective},
};


type Error = Box<dyn ff::Error>;

impl<M: TEModelParameters, ConstraintF: Field> ToConstraintField<ConstraintF> for TEAffine<M>
where
    M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<ConstraintF>, Error> {
        let mut x_fe = self.x.to_field_elements()?;
        let y_fe = self.y.to_field_elements()?;
        x_fe.extend_from_slice(&y_fe);
        Ok(x_fe)
    }
}

impl<M: TEModelParameters, ConstraintF: Field> ToConstraintField<ConstraintF> for TEProjective<M>
where
    M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<ConstraintF>, Error> {
        TEAffine::from(*self).to_field_elements()
    }
}

impl<M: SWModelParameters, ConstraintF: Field> ToConstraintField<ConstraintF> for SWAffine<M>
where
    M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<ConstraintF>, Error> {
        let mut x_fe = self.x.to_field_elements()?;
        let y_fe = self.y.to_field_elements()?;
        x_fe.extend_from_slice(&y_fe);
        Ok(x_fe)
    }
}

impl<M: SWModelParameters, ConstraintF: Field> ToConstraintField<ConstraintF> for SWProjective<M>
where
    M::BaseField: ToConstraintField<ConstraintF>,
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<ConstraintF>, Error> {
        SWAffine::from(*self).to_field_elements()
    }
}
