#[frame_support::pallet]
mod pallet {
    use frame_support::pallet_prelude::*;
    use frame_system::pallet_prelude::*;

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {}

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        #[pallet::call_index(0)]
        #[pallet::weight(0)]
        pub fn binary_search(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
            let res = data.binary_search(&0);
            if let Err(pos) = res {
                let _ = data[pos]; //~ WARN: possible index out of bounds
            }

            Ok(())
        }

        #[pallet::call_index(1)]
        #[pallet::weight(0)]
        pub fn binary_search_transform(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
            let res = data.binary_search(&0).inspect(|_| ());
            if let Err(pos) = res {
                let _ = data[pos]; //~ WARN: possible index out of bounds
            }

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
            Minimal::binary_search(RuntimeOrigin::signed(0), vec![0]);
        });
    }
}
