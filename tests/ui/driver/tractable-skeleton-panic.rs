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
        if val == 0 {
            panic!("no zeros!"); //~ WARN: no zeros!
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    pub struct MyConfig;
    impl Config for MyConfig {}

    fn do_something_test() {
        let origin = OriginFor::Simple;
        Pallet::<MyConfig>::do_something(origin, 1);
    }
}