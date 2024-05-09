//! A `FileLoader` that "virtually" adds an entry point module to the crate.

use rustc_data_structures::sync::Lrc;
use rustc_span::source_map::RealFileLoader;

use std::path::Path;
use std::path::PathBuf;

const ENTRY_POINT_MOD_NAME: &str = "__pallet_verifier_entry_points";

/// A `FileLoader` that "virtually" adds an entry point module to the crate.
pub struct EntryPointFileLoader {
    file_loader: RealFileLoader,
    root_path: PathBuf,
    entry_point_path: PathBuf,
    entry_point_content: String,
}

impl EntryPointFileLoader {
    pub fn new(root_path: PathBuf, entry_point_content: String) -> Self {
        let mut entry_point_path = root_path.clone();
        entry_point_path.set_file_name(format!("{ENTRY_POINT_MOD_NAME}.rs"));

        Self {
            file_loader: RealFileLoader,
            root_path,
            entry_point_path,
            entry_point_content,
        }
    }
}

impl rustc_span::source_map::FileLoader for EntryPointFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        if path == self.entry_point_path {
            true
        } else {
            self.file_loader.file_exists(path)
        }
    }

    fn read_file(&self, path: &Path) -> std::io::Result<String> {
        let content = if path == self.entry_point_path {
            self.entry_point_content.clone()
        } else {
            let mut file_content = self.file_loader.read_file(path)?;
            if path == self.root_path {
                file_content.push_str(&format!("mod {ENTRY_POINT_MOD_NAME};"));
            }
            file_content
        };
        std::io::Result::Ok(content)
    }

    fn read_binary_file(&self, path: &Path) -> std::io::Result<Lrc<[u8]>> {
        if path == self.entry_point_path {
            let mut bytes = Lrc::new_uninit_slice(self.entry_point_content.len());
            let data: &mut [std::mem::MaybeUninit<u8>] = Lrc::get_mut(&mut bytes).unwrap();
            for (idx, byte) in self.entry_point_content.as_bytes().iter().enumerate() {
                data[idx].write(*byte);
            }
            // SAFETY: We just wrote the exact number of bytes.
            Ok(unsafe { bytes.assume_init() })
        } else {
            self.file_loader.read_binary_file(path)
        }
    }
}
