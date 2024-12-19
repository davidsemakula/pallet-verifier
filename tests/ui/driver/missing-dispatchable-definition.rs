use std::marker::PhantomData;

pub mod pallet {
    use super::*;
    
    pub trait Config {}

    pub enum Call<T: Config> {
        __Ignore(PhantomData<T>),
        do_something { val: u8 },
    }

    pub struct Pallet<T: Config>(PhantomData<T>);
}
