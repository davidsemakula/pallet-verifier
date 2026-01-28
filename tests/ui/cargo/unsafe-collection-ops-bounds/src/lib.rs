extern crate alloc;

#[frame_support::pallet]
mod pallet {
    use alloc::collections::BTreeSet;

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
        pub fn len(origin: OriginFor<T>, data: BTreeSet<u8>) -> DispatchResult {
            let len = data.len();
            let _ = len + 1; //~ WARN: add with overflow

            Ok(())
        }

        #[pallet::call_index(1)]
        #[pallet::weight(0)]
        pub fn len_multiple(
            origin: OriginFor<T>,
            data1: Vec<u8>,
            data2: Vec<u8>,
            data3: Vec<u8>,
        ) -> DispatchResult {
            let len = data1.len() + data2.len() + data3.len(); //~ WARN: add with overflow

            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::collections::BTreeSet;

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
            Minimal::len(RuntimeOrigin::signed(0), BTreeSet::new());
        });
    }
}
