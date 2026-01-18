#[frame_support::pallet]
mod pallet {
    use core::ops::Range;

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
        pub fn counter(origin: OriginFor<T>, data: Range<u32>) -> DispatchResult {
            let mut count = 0usize;
            for _ in data {
                count += 1; //~ WARN: add with overflow
            }

            Ok(())
        }

        #[pallet::call_index(1)]
        #[pallet::weight(0)]
        pub fn enumerate(origin: OriginFor<T>, data: Range<u32>) -> DispatchResult {
            for (idx, _) in data.into_iter().enumerate() {
                let _ = idx + 1; //~ WARN: add with overflow
            }

            Ok(())
        }

        #[pallet::call_index(2)]
        #[pallet::weight(0)]
        pub fn count(origin: OriginFor<T>, data: Range<u32>) -> DispatchResult {
            let count = data.into_iter().count();
            let _ = count + 1; //~ WARN: add with overflow

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
            Minimal::counter(RuntimeOrigin::signed(0), 0..5);
        });
    }
}
