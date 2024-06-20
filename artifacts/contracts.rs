//! MIRAI "contracts" for some FRAME, Substrate and standard library functions for "more tractable" analysis.
//!
//! Ref: <https://github.com/facebookexperimental/MIRAI/blob/main/documentation/Overview.md#foreign-functions>

#![allow(unused)]
#![allow(nonstandard_style)]
#![allow(private_interfaces)]

macro_rules! noop {
    ($name:ident) => {
        pub fn $name() {}
    };
}

macro_rules! noop_result {
    ($name:ident, $res: ty) => {
        pub fn $name() -> $res {
            mirai_annotations::result!()
        }
    };
}

macro_rules! noop_result_custom_ty {
    ($name:ident) => {
        pub fn $name<T>() -> T {
            mirai_annotations::result!()
        }
    };
}

pub mod sp_io {
    pub mod storage {
        noop!(start_transaction);
        noop!(commit_transaction);
        noop!(rollback_transaction);

        noop!(set);
        noop_result_custom_ty!(get);
        noop!(clear);
        noop!(append);

        noop_result!(exists, bool);
        noop_result!(read, Option<u32>);
        noop_result_custom_ty!(clear_prefix);
        noop_result!(next_key, Option<Vec<u8>>);

        noop_result!(root, Vec<u8>);
        noop_result!(changes_root, Option<Vec<u8>>);
    }

    pub mod hashing {
        noop_result!(blake2_128, [u8; 16]);
        noop_result!(blake2_256, [u8; 32]);

        noop_result!(keccak_256, [u8; 32]);
        noop_result!(keccak_512, [u8; 64]);

        noop_result!(sha2_256, [u8; 32]);

        noop_result!(twox_64, [u8; 8]);
        noop_result!(twox_128, [u8; 16]);
        noop_result!(twox_256, [u8; 32]);
    }

    pub mod logging {
        noop!(log);
    }
}

pub mod alloc {
    pub mod alloc {
        noop_result!(exchange_malloc, *mut u8);
    }
}

pub mod std {
    pub mod thread {
        pub mod local {
            pub mod implement_std_thread_local_LocalKey_generic_par_T {
                noop_result_custom_ty!(try_with);
            }
        }
    }
}

pub mod log {
    pub mod __private_api {
        noop!(log);
    }
}
