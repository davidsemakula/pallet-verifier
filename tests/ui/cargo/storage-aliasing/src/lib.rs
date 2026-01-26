extern crate alloc;

#[frame_support::pallet]
mod pallet {
    use alloc::vec::Vec;

    use frame_support::pallet_prelude::*;
    use frame_system::pallet_prelude::*;

    use super::*;

    #[pallet::pallet]
    #[pallet::without_storage_info]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {}

    #[pallet::storage]
    pub type Collection<T: Config> = StorageValue<_, Vec<u8>, ValueQuery>;

    #[pallet::error]
    pub enum Error<T> {
        Duplicate,
    }

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        #[pallet::call_index(0)]
        #[pallet::weight(0)]
        pub fn try_insert(origin: OriginFor<T>, val: u8) -> DispatchResult {
            let res = Collection::<T>::get().binary_search(&val);
            if let Err(idx) = res {
                Collection::<T>::mutate(|c| c.insert(idx, val));
                Ok(())
            } else {
                Err(Error::<T>::Duplicate.into())
            }
        }

        #[pallet::call_index(1)]
        #[pallet::weight(0)]
        pub fn try_insert_transform(origin: OriginFor<T>, val: u8) -> DispatchResult {
            let idx = Collection::<T>::get()
                .binary_search(&val)
                .err()
                .ok_or(Error::<T>::Duplicate)?;
            Collection::<T>::mutate(|c| c.insert(idx, val));
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use frame_support::derive_impl;

    frame_support::construct_runtime!(
        pub enum Test
        {
            System: frame_system,
            Minimal: pallet,
        }
    );

    type Block = frame_system::mocking::MockBlock<Test>;

    #[derive_impl(frame_system::config_preludes::TestDefaultConfig as frame_system::pallet::DefaultConfig)]
    impl frame_system::Config for Test {
        type Block = Block;
    }

    impl pallet::Config for Test {}

    #[test]
    fn do_something_works() {
        use frame_support::sp_runtime::BuildStorage;
        let mut t = frame_system::GenesisConfig::<Test>::default()
            .build_storage()
            .unwrap();
        let mut ext = sp_io::TestExternalities::new(t);
        ext.execute_with(|| {
            System::set_block_number(1);
            Minimal::try_insert(RuntimeOrigin::signed(0), 1);
        });
    }
}
