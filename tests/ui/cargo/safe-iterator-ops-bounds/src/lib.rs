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
        pub fn counter(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
            let mut count = 0usize;
            for _ in data {
                // Number of iterations <= isize::MAX, so count is always < usize::MAX
                count += 1;
            }

            Ok(())
        }

        #[pallet::call_index(1)]
        #[pallet::weight(0)]
        pub fn counter_transform(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
            let mut count = 0usize;
            for _ in data
                .into_iter()
                .filter(|x| *x < 100)
                .map(|x| x)
                .take_while(|_| true)
            {
                // Number of iterations <= isize::MAX, so count is always < usize::MAX
                count += 1;
            }

            Ok(())
        }

        #[pallet::call_index(2)]
        #[pallet::weight(0)]
        pub fn counter_chain(
            origin: OriginFor<T>,
            data1: Vec<u8>,
            data2: Vec<u8>,
        ) -> DispatchResult {
            let mut count = 0usize;
            for _ in std::iter::empty().chain(data1.iter()).chain(data2.iter()) {
                // Number of iterations <= 2 * isize::MAX, so count is always < usize::MAX
                count += 1;
            }

            Ok(())
        }

        #[pallet::call_index(3)]
        #[pallet::weight(0)]
        pub fn enumerate(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
            for (idx, _) in data.iter().enumerate() {
                // Number of iterations <= isize::MAX, so idx is always < usize::MAX
                let _ = idx + 1;
            }

            Ok(())
        }

        #[pallet::call_index(4)]
        #[pallet::weight(0)]
        pub fn enumerate_transform(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
            for (idx, _) in data
                .into_iter()
                .filter(|x| *x < 100)
                .map(|x| x)
                .take_while(|_| true)
                .enumerate()
            {
                // Number of iterations <= isize::MAX, so idx is always < usize::MAX
                let _ = idx + 1;
            }

            Ok(())
        }

        #[pallet::call_index(5)]
        #[pallet::weight(0)]
        pub fn enumerate_chain(
            origin: OriginFor<T>,
            data1: Vec<u8>,
            data2: Vec<u8>,
        ) -> DispatchResult {
            for (idx, _) in std::iter::empty()
                .chain(data1.iter())
                .chain(data2.iter())
                .enumerate()
            {
                // Number of iterations <= 2 * isize::MAX, so idx is always < usize::MAX
                let _ = idx + 1;
            }

            Ok(())
        }

        #[pallet::call_index(6)]
        #[pallet::weight(0)]
        pub fn position(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
            let pos = data.iter().position(|item| *item == 0);
            if let Some(pos) = pos {
                // pos is always in bounds.
                let _ = data[pos];
            }

            Ok(())
        }

        #[pallet::call_index(7)]
        #[pallet::weight(0)]
        pub fn rposition(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
            let pos = data.iter().rposition(|item| *item == 0);
            if let Some(pos) = pos {
                // pos is always in bounds.
                let _ = data[pos];
            }

            Ok(())
        }

        #[pallet::call_index(8)]
        #[pallet::weight(0)]
        pub fn position_complex(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
            let pos = data.iter().position(|item| *item == 0);
            match pos {
                Some(pos) if data.len() > pos + 1 => {
                    // pos + 1 can't overflow because data.len() <= isize::MAX,
                    // and it's in bounds due to the match guard.
                    let _ = data[pos + 1];
                }
                Some(pos) => {
                    // pos is always in bounds.
                    let _ = data[pos];
                }
                None => (),
            }

            Ok(())
        }

        #[pallet::call_index(9)]
        #[pallet::weight(0)]
        pub fn position_unwrap_or(origin: OriginFor<T>, mut data: Vec<u8>) -> DispatchResult {
            let pos = data
                .iter()
                .position(|item| *item == 0)
                .unwrap_or(data.len());
            // pos is always <= data.len()
            data.insert(pos, 255);

            Ok(())
        }

        #[pallet::call_index(10)]
        #[pallet::weight(0)]
        pub fn position_unwrap_or_else(origin: OriginFor<T>, mut data: Vec<u8>) -> DispatchResult {
            let pos = data
                .iter()
                .position(|item| *item == 0)
                .unwrap_or_else(|| data.len());
            // pos is always <= data.len()
            data.insert(pos, 255);

            Ok(())
        }

        #[pallet::call_index(11)]
        #[pallet::weight(0)]
        pub fn count(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
            // Number of elements <= isize::MAX, so count is always < usize::MAX
            let count = data.iter().count();
            let _ = count + 1;

            Ok(())
        }

        #[pallet::call_index(12)]
        #[pallet::weight(0)]
        pub fn count_transform(origin: OriginFor<T>, data: Vec<u8>) -> DispatchResult {
            // Number of elements <= isize::MAX, so count is always < usize::MAX
            let count = data
                .into_iter()
                .filter(|x| *x < 100)
                .map(|x| x)
                .take_while(|_| true)
                .count();
            let _ = count + 1;

            Ok(())
        }

        #[pallet::call_index(13)]
        #[pallet::weight(0)]
        pub fn count_chain(origin: OriginFor<T>, data1: Vec<u8>, data2: Vec<u8>) -> DispatchResult {
            // Number of elements <= 2 * isize::MAX, so count is always < usize::MAX
            let count = std::iter::empty()
                .chain(data1.iter())
                .chain(data2.iter())
                .count();
            let _ = count + 1;

            Ok(())
        }

        #[pallet::call_index(14)]
        #[pallet::weight(0)]
        pub fn count_multiple(
            origin: OriginFor<T>,
            data1: Vec<u8>,
            data2: Vec<u8>,
        ) -> DispatchResult {
            // Number of total elements <= 2 * isize::MAX, so count is always < usize::MAX
            let count = data1.iter().count() + data2.iter().count();

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
            Minimal::counter(RuntimeOrigin::signed(0), vec![0]);
        });
    }
}
