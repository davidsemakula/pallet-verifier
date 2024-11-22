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

pub mod core {
    pub mod fmt {
        pub mod rt {
            pub mod implement_core_fmt_rt_Argument {
                noop_result_custom_ty!(new);
            }
        }
    }

    pub mod iter {
        pub mod adapters {
            pub mod enumerate {
                pub mod implement_core_iter_adapters_enumerate_Enumerate_generic_par_I {
                    noop_result_custom_ty!(next);
                }
            }
        }
    }

    pub mod ops {
        pub mod arith {
            macro_rules! div {
                ($name:ident, $ty: ty) => {
                    pub mod $name {
                        pub fn div(x: $ty, y: $ty) -> $ty {
                            mirai_annotations::precondition!(y != 0);
                            mirai_annotations::result!()
                        }
                        pub fn div_assign(x: $ty, y: $ty) {
                            mirai_annotations::precondition!(y != 0);
                        }
                    }
                };
            }

            div!(implement_usize, usize);
            div!(implement_u8, u8);
            div!(implement_u16, u16);
            div!(implement_u32, u32);
            div!(implement_u64, u64);
            div!(implement_u128, u128);
        }
    }

    pub mod slice {
        pub mod iter {
            pub mod implement_core_slice_iter_Iter_generic_par_T {
                noop_result_custom_ty!(next);
            }
        }

        pub mod sort {
            noop!(merge_sort);
        }
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
pub mod frame_support {
    pub mod storage {
        pub mod unhashed {
            noop_result_custom_ty!(get);
        }

        pub mod child {
            noop_result_custom_ty!(get);
        }
    }
}

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

pub mod sp_core {
    pub mod bandersnatch {
        pub mod ring_vrf {
            pub mod implement_sp_core_bandersnatch_ring_vrf_RingVerifierData {
                noop_result_custom_ty!(decode);
            }

            pub mod implement_sp_core_bandersnatch_ring_vrf_RingVrfSignature {
                noop_result_custom_ty!(ring_vrf_verify);
            }
        }

        pub mod vrf {
            pub mod implement_sp_core_bandersnatch_vrf_VrfInput {
                noop_result_custom_ty!(new);
            }

            pub mod implement_sp_core_bandersnatch_vrf_VrfPreOutput {
                noop_result_custom_ty!(make_bytes);
            }
        }
    }

    pub mod sr25519 {
        pub mod vrf {
            pub mod implement_sp_core_sr25519_vrf_VrfProof {
                noop_result!(encode, Vec<u8>);
                noop_result_custom_ty!(decode);
            }
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

    pub mod logging {
        noop!(log);
    }
}

pub mod sp_crypto_hashing {
    noop_result!(blake2_128, [u8; 16]);
    noop_result!(blake2_256, [u8; 32]);

    noop_result!(keccak_256, [u8; 32]);
    noop_result!(keccak_512, [u8; 64]);

    noop_result!(sha2_256, [u8; 32]);

    noop_result!(twox_64, [u8; 8]);
    noop_result!(twox_128, [u8; 16]);
    noop_result!(twox_256, [u8; 32]);
}

pub mod sp_npos_elections {
    pub mod reduce {
        noop_result!(reduce, u32);
    }
}

/* Common crates in Substrate and FRAME primitives */
pub mod bandersnatch_vrfs {
    pub mod ring {
        noop_result_custom_ty!(make_ring_verifier);
    }

    pub mod implement_bandersnatch_vrfs_Message {
        noop_result_custom_ty!(into_vrf_input);
    }
}

pub mod log {
    pub mod __private_api {
        noop!(log);
    }
}

pub mod memory_db {
    pub mod implement_memory_db_MemoryDB_generic_par_H_generic_par_KF_generic_par_T {
        noop_result_custom_ty!(get);
        noop_result!(contains, bool);
        noop!(emplace);
        noop_result_custom_ty!(insert);
        noop!(remove);
    }
}

pub mod parity_scale_codec {
    pub mod codec {
        pub trait Encode {
            noop_result!(, encode, Vec<u8>);
        }
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

pub mod schnorrkel {
    pub mod vrf {
        pub mod implement_schnorrkel_vrf_VRFProof {
            noop_result!(to_bytes, [u8; 64]);
            noop_result_custom_ty!(from_bytes);
        }
    }
}

pub mod trie_db {
    pub mod lookup {
        pub mod implement_trie_db_lookup_Lookup_generic_par_L_generic_par_Q {
            noop_result_custom_ty!(lookup_first_descendant);
            noop_result_custom_ty!(look_up);
            noop_result_custom_ty!(look_up_hash);
        }
    }

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

pub mod wasmi {
    pub mod engine {
        mod config {
            pub mod implement_wasmi_engine_config_Config {
                noop_result_custom_ty!(set_stack_limits);
                noop_result_custom_ty!(set_cached_stacks);
                noop_result_custom_ty!(wasm_mutable_global);
                noop_result_custom_ty!(wasm_sign_extension);
                noop_result_custom_ty!(wasm_saturating_float_to_int);
                noop_result_custom_ty!(wasm_multi_value);
                noop_result_custom_ty!(wasm_bulk_memory);
                noop_result_custom_ty!(wasm_reference_types);
                noop_result_custom_ty!(wasm_tail_call);
                noop_result_custom_ty!(wasm_extended_const);
                noop_result_custom_ty!(floats);
                noop_result_custom_ty!(consume_fuel);
                noop_result_custom_ty!(ignore_custom_sections);
                noop_result_custom_ty!(compilation_mode);
                noop_result_custom_ty!(enforced_limits);

                noop_result_custom_ty!(stack_limits);
                noop_result_custom_ty!(cached_stacks);

                noop_result_custom_ty!(get_consume_fuel);
                noop_result_custom_ty!(get_ignore_custom_sections);
                noop_result_custom_ty!(fuel_costs);
                noop_result_custom_ty!(get_compilation_mode);
                noop_result_custom_ty!(get_enforced_limits);
                noop_result_custom_ty!(wasm_features);
            }
        }

        pub mod implement_wasmi_engine_Engine {
            noop_result_custom_ty!(new);
            noop_result_custom_ty!(weak);
            noop_result_custom_ty!(config);
            noop_result_custom_ty!(same);

            noop_result_custom_ty!(alloc_func_type);
            noop_result_custom_ty!(resolve_func_type);
            noop_result_custom_ty!(alloc_funcs);

            noop_result_custom_ty!(translate_func);
            noop_result_custom_ty!(get_translation_allocs);
            noop_result_custom_ty!(get_allocs);
            noop_result_custom_ty!(recycle_translation_allocs);
            noop_result_custom_ty!(recycle_allocs);
            noop_result_custom_ty!(resolve_instr);
            noop_result_custom_ty!(execute_func);
            noop_result_custom_ty!(execute_func_resumable);
            noop_result_custom_ty!(resume_func);
            noop_result_custom_ty!(recycle_stack);
        }
    }

    pub mod linker {
        pub mod implement_wasmi_linker_Linker_generic_par_T {
            noop_result_custom_ty!(new);
            noop_result_custom_ty!(build);
            noop_result_custom_ty!(engine);
            noop_result_custom_ty!(define);
            noop_result_custom_ty!(func_new);
            noop_result_custom_ty!(func_wrap);
            noop_result_custom_ty!(get);
            noop_result_custom_ty!(instantiate);
        }
    }

    pub mod memory {
        pub mod implement_wasmi_memory_Memory {
            noop_result_custom_ty!(new);
            noop_result_custom_ty!(new_static);
            noop_result_custom_ty!(ty);
            noop_result!(size, u32);
            noop_result_custom_ty!(grow);
            noop_result_custom_ty!(data);
            noop_result_custom_ty!(data_mut);
            noop_result_custom_ty!(data_and_store_mut);
            noop_result!(data_ptr, *mut u8);
            noop_result!(data_size, usize);
            noop_result_custom_ty!(read);
            noop_result_custom_ty!(write);

            noop_result_custom_ty!(from_inner);
            noop_result_custom_ty!(as_inner);

            noop_result_custom_ty!(dynamic_ty);
        }
    }

    pub mod module {
        pub mod implement_wasmi_module_Module {
            noop_result_custom_ty!(new);
            noop_result_custom_ty!(new_streaming);
            noop_result_custom_ty!(new_unchecked);
            noop_result_custom_ty!(new_streaming_unchecked);
            noop_result_custom_ty!(engine);
            noop_result_custom_ty!(validate);
            noop_result_custom_ty!(imports);
            noop_result_custom_ty!(exports);
            noop_result_custom_ty!(get_export);
            noop_result_custom_ty!(custom_sections);

            noop_result!(len_funcs, usize);
            noop_result!(len_tables, usize);
            noop_result!(len_memories, usize);
            noop_result!(len_globals, usize);
            noop_result_custom_ty!(func_types_cloned);
            noop_result_custom_ty!(internal_funcs);
        }
    }

    pub mod store {
        pub mod implement_wasmi_store_Store_generic_par_T {
            noop_result_custom_ty!(new);
            noop_result_custom_ty!(engine);
            noop_result_custom_ty!(data);
            noop_result_custom_ty!(data_mut);
            noop_result_custom_ty!(into_data);
            noop!(limiter);
            noop_result_custom_ty!(get_fuel);
            noop_result_custom_ty!(set_fuel);

            noop_result_custom_ty!(check_new_instances_limit);
            noop_result_custom_ty!(check_new_memories_limit);
            noop_result_custom_ty!(check_new_tables_limit);
            noop_result_custom_ty!(store_inner_and_resource_limiter_ref);

            noop_result_custom_ty!(alloc_trampoline);
            noop_result_custom_ty!(resolve_memory_and_state_mut);
            noop_result_custom_ty!(resolve_trampoline);
        }
    }
}
