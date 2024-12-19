use std::marker::PhantomData;
use std::num::Wrapping;

pub mod pallet {
    use super::*;

    pub trait Config {}

    pub enum Call<T: Config> {
        __Ignore(PhantomData<T>),
        do_something { val: Wrapping<u8> },
    }

    pub struct Pallet<T: Config>(PhantomData<T>);

    pub enum OriginFor<T> {
        Simple,
        Complex(T),
    }

    impl<T: Config> Pallet<T> {
        pub fn do_something(
            origin: OriginFor<T>,
            val: Wrapping<u8>,
        ) {
            val + Wrapping(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::pallet::*;

    pub struct MyConfig;
    impl Config for MyConfig {}

    fn do_something_test() {
        let origin = OriginFor::Simple;
        Pallet::<MyConfig>::do_something(origin, Wrapping(0));
    }
}