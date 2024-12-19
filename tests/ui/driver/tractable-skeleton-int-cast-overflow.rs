use std::marker::PhantomData;

pub mod pallet {
    use super::*;

    pub trait Config {}

    pub enum Call<T: Config> {
        __Ignore(PhantomData<T>),
        do_something { val: u16 },
    }

    pub struct Pallet<T: Config>(PhantomData<T>);

    pub enum OriginFor<T> {
        Simple,
        Complex(T),
    }

    impl<T: Config> Pallet<T> {
        pub fn do_something(
            origin: OriginFor<T>,
            val: u16,
        ) {
            let val2 = val as u8; //~ WARN: cast with overflow
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
        Pallet::<MyConfig>::do_something(origin, 0);
    }
}