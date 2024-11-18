//! A `FileLoader` that "virtually" adds "analysis-only" external crates and modules to a crate.

#![allow(clippy::type_complexity)]

use rustc_data_structures::sync::Lrc;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_span::source_map::RealFileLoader;

use std::path::{Path, PathBuf};

use itertools::Itertools;

/// A `FileLoader` that "virtually" adds "analysis-only" external crates and modules to a crate.
pub struct VirtualFileLoader {
    file_loader: RealFileLoader,
    // Source map for "virtual" contents for root paths.
    root_source_map: FxHashMap<
        // The root path.
        PathBuf,
        (
            // base "virtual" content for root path.
            Option<String>,
            // feature declarations.
            Option<String>,
            // `extern crate` declarations.
            Option<String>,
            // "virtual" `mod` declarations.
            Option<String>,
        ),
    >,
    // Source map for content of "virtual" modules.
    mod_source_map: FxHashMap<PathBuf, String>,
}

impl VirtualFileLoader {
    /// Creates a "virtual" file loader.
    pub fn new(
        source_map_def: FxHashMap<
            // The root path.
            PathBuf,
            (
                // base "virtual" content for root path.
                Option<String>,
                // names of features to enable.
                Option<FxHashSet<&str>>,
                // names of external crates to declare.
                Option<FxHashSet<&str>>,
                // `name` -> `content` map for "virtual" modules.
                Option<FxHashMap<&str, String>>,
            ),
        >,
    ) -> Self {
        // Composes root and module source "virtual" maps based on the given definition.
        let mut root_source_map = FxHashMap::default();
        let mut mod_source_map = FxHashMap::default();
        for (root_path, (root_content, features, extern_crates, virtual_mods)) in source_map_def {
            let feature_decls = features
                .filter(|features| !features.is_empty())
                .map(|features| {
                    features
                        .iter()
                        .map(|feature| format!("#![feature({feature})]"))
                        .join("\n")
                });
            let extern_crate_decls = extern_crates
                .filter(|extern_crates| !extern_crates.is_empty())
                .map(|extern_crates| {
                    extern_crates
                        .iter()
                        .map(|extern_crate| format!("extern crate {extern_crate};"))
                        .join("\n")
                });
            let mut virtual_mod_decls = FxHashSet::default();
            if let Some(virtual_mods) = virtual_mods {
                for (name, content) in virtual_mods {
                    let mut mod_path = root_path.clone();
                    mod_path.set_file_name(format!("{name}.rs"));
                    mod_source_map.insert(mod_path, content);
                    virtual_mod_decls.insert(format!("mod {name};"));
                }
            }
            let virtual_mod_decls_str =
                (!virtual_mod_decls.is_empty()).then_some(virtual_mod_decls.into_iter().join("\n"));
            root_source_map.insert(
                root_path,
                (
                    root_content,
                    feature_decls,
                    extern_crate_decls,
                    virtual_mod_decls_str,
                ),
            );
        }

        Self {
            file_loader: RealFileLoader,
            root_source_map,
            mod_source_map,
        }
    }

    /// Returns "virtual" content for the specified path.
    fn base_virtual_content(&self, path: &Path) -> Option<&String> {
        let virtual_root_content = self
            .root_source_map
            .get(path)
            .and_then(|(root_content, ..)| root_content.as_ref());
        virtual_root_content.or_else(|| self.mod_source_map.get(path))
    }

    /// Appends extra "virtual" content for the specified path to the given base content (if necessary).
    fn append_extra_virtual_content(&self, path: &Path, base_content: &mut String) {
        if let Some((_, feature_decls, extern_crate_decls, virtual_mod_decls)) =
            self.root_source_map.get(path)
        {
            if let Some(decls) = feature_decls.as_deref() {
                *base_content = format!("{decls}\n{base_content}");
            }
            if let Some(decls) = extern_crate_decls.as_deref() {
                base_content.push_str(decls);
            }
            if let Some(decls) = virtual_mod_decls.as_deref() {
                base_content.push_str(decls);
            }
        }
    }
}

impl rustc_span::source_map::FileLoader for VirtualFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        let has_virtual_root_content = self
            .root_source_map
            .get(path)
            .is_some_and(|(content, ..)| content.is_some());
        if has_virtual_root_content || self.mod_source_map.contains_key(path) {
            true
        } else {
            self.file_loader.file_exists(path)
        }
    }

    fn read_file(&self, path: &Path) -> std::io::Result<String> {
        let mut content = if let Some(content) = self.base_virtual_content(path) {
            content.clone()
        } else {
            self.file_loader.read_file(path)?
        };
        self.append_extra_virtual_content(path, &mut content);
        std::io::Result::Ok(content)
    }

    fn read_binary_file(&self, path: &Path) -> std::io::Result<Lrc<[u8]>> {
        if let Some(mut content) = self.base_virtual_content(path).cloned() {
            self.append_extra_virtual_content(path, &mut content);

            let mut bytes = Lrc::new_uninit_slice(content.len());
            let data: &mut [std::mem::MaybeUninit<u8>] = Lrc::get_mut(&mut bytes).unwrap();
            for (idx, byte) in content.as_bytes().iter().enumerate() {
                data[idx].write(*byte);
            }
            // SAFETY: We just wrote the exact number of bytes.
            Ok(unsafe { bytes.assume_init() })
        } else {
            self.file_loader.read_binary_file(path)
        }
    }
}
