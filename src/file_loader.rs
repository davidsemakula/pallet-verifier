//! A `FileLoader` that "virtually" adds "entry points" and "contracts" modules to the crate.
//!
//! See [`crate::EntryPointsCallbacks`] doc.

use rustc_data_structures::sync::Lrc;
use rustc_span::source_map::RealFileLoader;

use std::path::Path;
use std::path::PathBuf;

use crate::{CONTRACTS_MOD_NAME, ENTRY_POINTS_MOD_NAME};

/// A `FileLoader` that "virtually" adds "entry points" and "contracts" modules to the crate.
///
/// See [`crate::EntryPointsCallbacks`] doc.
pub struct VirtualFileLoader {
    file_loader: RealFileLoader,
    root_path: PathBuf,
    entry_points_path: PathBuf,
    entry_points_content: String,
    contracts: Option<(PathBuf, String)>,
}

impl VirtualFileLoader {
    pub fn new(
        root_path: PathBuf,
        entry_points_content: String,
        contracts: Option<String>,
    ) -> Self {
        let mut entry_points_path = root_path.clone();
        entry_points_path.set_file_name(format!("{ENTRY_POINTS_MOD_NAME}.rs"));

        let contracts = contracts.map(|contracts| {
            let mut contracts_path = root_path.clone();
            contracts_path.set_file_name(format!("{CONTRACTS_MOD_NAME}.rs"));
            (contracts_path, contracts)
        });

        Self {
            file_loader: RealFileLoader,
            root_path,
            entry_points_path,
            entry_points_content,
            contracts,
        }
    }
}

impl rustc_span::source_map::FileLoader for VirtualFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        if path == self.entry_points_path
            || self
                .contracts
                .as_ref()
                .is_some_and(|(contracts_path, _)| contracts_path == path)
        {
            true
        } else {
            self.file_loader.file_exists(path)
        }
    }

    fn read_file(&self, path: &Path) -> std::io::Result<String> {
        let content = if path == self.entry_points_path {
            self.entry_points_content.clone()
        } else if self
            .contracts
            .as_ref()
            .is_some_and(|(contracts_path, _)| contracts_path == path)
        {
            self.contracts
                .as_ref()
                .map(|(_, content)| content.clone())
                .unwrap_or_default()
        } else {
            let mut file_content = self.file_loader.read_file(path)?;
            if path == self.root_path {
                file_content.push_str(&format!("mod {ENTRY_POINTS_MOD_NAME};"));
                if self.contracts.is_some() {
                    file_content.push_str(&format!("\npub mod {CONTRACTS_MOD_NAME};"));
                }
            }
            file_content
        };
        std::io::Result::Ok(content)
    }

    fn read_binary_file(&self, path: &Path) -> std::io::Result<Lrc<[u8]>> {
        if path == self.entry_points_path
            || self
                .contracts
                .as_ref()
                .is_some_and(|(contracts_path, _)| contracts_path == path)
        {
            let content = if path == self.entry_points_path {
                self.entry_points_content.as_str()
            } else {
                self.contracts
                    .as_ref()
                    .map(|(_, content)| content.as_str())
                    .unwrap_or_default()
            };
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
