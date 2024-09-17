//! A `FileLoader` that "virtually" adds "analysis-only" external crates and modules to a crate.

use rustc_data_structures::sync::Lrc;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_span::source_map::RealFileLoader;

use std::path::{Path, PathBuf};

use itertools::Itertools;

/// A `FileLoader` that "virtually" adds "analysis-only" external crates and modules to a crate.
pub struct VirtualFileLoader {
    file_loader: RealFileLoader,
    root_path: PathBuf,
    root_content: Option<String>,
    extern_crate_decls: Option<String>,
    virtual_mod_decls: Option<String>,
    // `path` -> `content` map for "virtual" modules.
    virtual_mod_contents: FxHashMap<PathBuf, String>,
}

impl VirtualFileLoader {
    /// Creates a "virtual" file loader.
    pub fn new(
        root_path: PathBuf,
        root_content: Option<String>,
        extern_crates: Option<&FxHashSet<&str>>,
        // `name` -> `content` map for "virtual" modules.
        virtual_mods: Option<FxHashMap<&str, String>>,
    ) -> Self {
        let extern_crate_decls = extern_crates
            .filter(|extern_crates| !extern_crates.is_empty())
            .map(|extern_crates| {
                extern_crates
                    .iter()
                    .map(|extern_crate| format!("extern crate {extern_crate};"))
                    .join("\n")
            });
        let mut virtual_mod_decls = FxHashSet::default();
        let mut virtual_mod_contents = FxHashMap::default();
        if let Some(virtual_mods) = virtual_mods {
            for (name, content) in virtual_mods {
                let mut mod_path = root_path.clone();
                mod_path.set_file_name(format!("{name}.rs"));
                virtual_mod_contents.insert(mod_path, content);
                virtual_mod_decls.insert(format!("mod {name};"));
            }
        }

        Self {
            file_loader: RealFileLoader,
            root_path,
            root_content,
            extern_crate_decls,
            virtual_mod_decls: (!virtual_mod_decls.is_empty())
                .then_some(virtual_mod_decls.into_iter().join("\n")),
            virtual_mod_contents,
        }
    }

    /// Returns "virtual" content for the specified path.
    fn virtual_content(&self, path: &Path) -> Option<&String> {
        self.virtual_mod_contents.get(path).or_else(|| {
            if path == self.root_path && self.root_content.is_some() {
                self.root_content.as_ref()
            } else {
                None
            }
        })
    }
}

impl rustc_span::source_map::FileLoader for VirtualFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        if self.virtual_mod_contents.contains_key(path)
            || (path == self.root_path && self.root_content.is_some())
        {
            true
        } else {
            self.file_loader.file_exists(path)
        }
    }

    fn read_file(&self, path: &Path) -> std::io::Result<String> {
        let mut content = if let Some(content) = self.virtual_content(path) {
            content.clone()
        } else {
            self.file_loader.read_file(path)?
        };
        if path == self.root_path {
            if let Some(decls) = self.extern_crate_decls.as_deref() {
                content.push_str(decls);
            }
            if let Some(decls) = self.virtual_mod_decls.as_deref() {
                content.push_str(decls);
            }
        }
        std::io::Result::Ok(content)
    }

    fn read_binary_file(&self, path: &Path) -> std::io::Result<Lrc<[u8]>> {
        if let Some(content) = self.virtual_content(path) {
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
