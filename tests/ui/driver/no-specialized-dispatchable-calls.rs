use std::marker::PhantomData;

pub trait Config {}

pub enum Call<T: Config> {
    __Ignore(PhantomData<T>),
    do_something { val: u8 },
}

pub struct Pallet<T: Config>(PhantomData<T>);

pub enum OriginFor<T> {
    Simple,
    Complex(T),
}

impl<T: Config> Pallet<T> {
    pub fn do_something(
        origin: OriginFor<T>,
        val: u8,
    ) {
        // do something
    }
}