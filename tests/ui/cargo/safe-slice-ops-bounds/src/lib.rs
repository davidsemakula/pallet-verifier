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
            if let Ok(pos) = res {
                // pos is always in bounds.
                let _ = data[pos];
            }

            Ok(())
        }

        #[pallet::call_index(1)]
        #[pallet::weight(0)]
        pub fn binary_search_transform(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
            let res = data.binary_search(&0).inspect(|_| ());
            if let Ok(pos) = res {
                // pos is always in bounds, because inspect doesn't change the Result::Ok variant.
                let _ = data[pos];
            }

            Ok(())
        }

        #[pallet::call_index(2)]
        #[pallet::weight(0)]
        pub fn binary_search_by(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
            let res = data.binary_search_by(|item| item.cmp(&10));
            if let Ok(pos) = res {
                // pos is always in bounds.
                let _ = data[pos];
            }

            Ok(())
        }

        #[pallet::call_index(3)]
        #[pallet::weight(0)]
        pub fn binary_search_by_key(origin: OriginFor<T>, data: Vec<(u8, u8)>) -> DispatchResult {
            let res = data.binary_search_by_key(&0, |&(x, y)| x);
            if let Ok(pos) = res {
                // pos is always in bounds.
                let _ = data[pos];
            }

            Ok(())
        }

        #[pallet::call_index(4)]
        #[pallet::weight(0)]
        pub fn partition_point(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
            // Number of elements <= isize::MAX, so pos is always < usize::MAX
            let pos = data.partition_point(|item| *item == 0);
            let _ = pos + 1;

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
