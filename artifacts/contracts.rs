//! MIRAI "contracts" for some FRAME, Substrate and standard library functions for "more tractable" analysis.
//!
//! Ref: <https://github.com/facebookexperimental/MIRAI/blob/main/documentation/Overview.md#foreign-functions>

#![allow(unused)]
#![allow(nonstandard_style)]
#![allow(private_interfaces)]

macro_rules! noop {
    ($name:ident) => {
        noop!(pub, $name);
    };
    ($vis: vis, $name:ident) => {
        $vis fn $name() {}
    };
}

macro_rules! noop_result {
    ($name:ident, $res: ty) => {
        noop_result!(pub, $name, $res);
    };
    ($vis: vis, $name:ident, $res: ty) => {
        $vis fn $name() -> $res {
            mirai_annotations::result!()
        }
    };
}

macro_rules! noop_result_custom_ty {
    ($name:ident) => {
        noop_result_custom_ty!(pub, $name);
    };
    ($vis: vis, $name:ident) => {
        $vis fn $name<T>() -> T {
            mirai_annotations::result!()
        }
    };
}

/* Rust standard library */
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

/* Substrate and FRAME primitives */
pub mod sp_arithmetic {
    pub mod biguint {
        noop_result!(add_single, (u32, u32));
        noop_result!(mul_single, u64);
        noop_result!(split, (u32, u32));
    }

    pub mod helpers_128bit {
        noop_result!(gcd, u128);
        noop_result!(multiply_by_rational_with_rounding, Option<u128>);
        noop_result!(split, (u64, u64));
        noop_result!(sqrt, u128);
        noop_result_custom_ty!(to_big_uint);
    }

    pub mod per_things {
        pub trait PerThing {
            noop_result_custom_ty!(, square);

            noop_result_custom_ty!(, mul_floor);
            noop_result_custom_ty!(, mul_ceil);

            noop_result_custom_ty!(, saturating_reciprocal_mul);
            noop_result_custom_ty!(, saturating_reciprocal_mul_floor);
            noop_result_custom_ty!(, saturating_reciprocal_mul_ceil);

            noop_result_custom_ty!(, from_rational);
            noop_result_custom_ty!(, from_rational_approximation);
        }

        macro_rules! per_thing {
            ($name:ident, $ty: ty) => {
                pub mod $name {
                    noop_result_custom_ty!(from_parts);
                    noop_result_custom_ty!(from_percent);
                    noop_result_custom_ty!(from_float);
                    noop_result_custom_ty!(from_rational);
                    noop_result_custom_ty!(from_rational_approximation);
                    noop_result_custom_ty!(from_perthousand);

                    noop_result!(deconstruct, $ty);

                    noop_result_custom_ty!(mul);
                    noop_result_custom_ty!(div);
                    noop_result_custom_ty!(pow);
                    noop_result_custom_ty!(square);

                    noop_result_custom_ty!(int_mul);
                    noop_result!(int_div, $ty);

                    noop_result_custom_ty!(mul_floor);
                    noop_result_custom_ty!(mul_ceil);

                    noop_result_custom_ty!(saturating_reciprocal_mul);
                    noop_result_custom_ty!(saturating_reciprocal_mul_floor);
                    noop_result_custom_ty!(saturating_reciprocal_mul_ceil);
                    noop_result_custom_ty!(saturating_div);
                }
            };
        }

        per_thing!(implement_sp_arithmetic_per_things_Percent, u8);
        per_thing!(implement_sp_arithmetic_per_things_PerU16, u16);
        per_thing!(implement_sp_arithmetic_per_things_Permill, u32);
        per_thing!(implement_sp_arithmetic_per_things_Perbill, u32);
        per_thing!(implement_sp_arithmetic_per_things_Perquintill, u64);
    }

    pub mod traits {
        pub mod implement_generic_par_T {
            noop_result_custom_ty!(saturating_mul);
            noop_result_custom_ty!(saturating_pow);
        }
    }
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

pub mod sp_npos_elections {
    pub mod reduce {
        noop_result!(reduce, u32);
    }
}

/* Common crates in Substrate and FRAME primitives */
pub mod log {
    pub mod __private_api {
        noop!(log);
    }
}

pub mod primitive_types {
    macro_rules! primitive_type {
        ($name:ident) => {
            pub mod $name {
                noop_result_custom_ty!(div_mod);
                noop_result_custom_ty!(integer_sqrt);
                noop_result_custom_ty!(pow);
                noop_result_custom_ty!(overflowing_pow);
                noop_result_custom_ty!(checked_pow);

                noop_result_custom_ty!(overflowing_mul);
                noop_result_custom_ty!(saturating_mul);
                noop_result_custom_ty!(checked_mul);
                noop_result_custom_ty!(checked_div);
                noop_result_custom_ty!(checked_rem);
                noop_result_custom_ty!(full_mul);

                noop_result_custom_ty!(div);
                noop!(div_assign);

                noop_result_custom_ty!(mul);
                noop!(mul_assign);
            }
        };
    }

    primitive_type!(implement_primitive_types_U128);
    primitive_type!(implement_primitive_types_U256);
    primitive_type!(implement_primitive_types_U512);
}

pub mod trie_db {
    pub mod triedbmut {
        pub mod implement_trie_db_triedbmut_TrieDBMut_generic_par_L {
            noop_result_custom_ty!(db);
            noop_result_custom_ty!(db_mut);
            noop!(commit);
            noop!(drop);
            noop_result_custom_ty!(root);
            noop_result!(is_empty, bool);
            noop_result_custom_ty!(get);
            noop_result_custom_ty!(insert);
            noop_result_custom_ty!(remove);
            noop_result_custom_ty!(contains);
        }
    }
}
