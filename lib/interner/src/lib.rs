//! A string interning implementation
//!
//! Use this if you want to statically allocate `&str` values and deduplicate them.

use std::{
    collections::HashSet,
    sync::{OnceLock, PoisonError, RwLock},
};

/// Like [`Interner`], but able to be used as a `static` variable.
///
/// There is some computational overhead associated with the necessary locking, so prefer
/// [`Interner`] if you do not need this functionality.
pub struct LockedInterner {
    inner: RwLock<OnceLock<Interner>>,
}
impl Default for LockedInterner {
    fn default() -> Self {
        Self::new()
    }
}

impl LockedInterner {
    /// Construct a new string interner
    ///
    /// Unlike [`Interner::new`], this function is `const`.
    pub const fn new() -> Self {
        Self {
            inner: RwLock::new(OnceLock::new()),
        }
    }

    /// Get an existing interned string, or return `None` if not interned
    pub fn get(&self, s: impl AsRef<str>) -> Option<&'static str> {
        self.inner
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .get_or_init(Interner::new)
            .get(s)
    }

    /// Get an existing interned string, or intern it if not already interned
    pub fn intern(&self, s: impl AsRef<str>) -> &'static str {
        let s = s.as_ref();
        if let Some(interned) = self.get(s) {
            interned
        } else {
            let mut guard = self.inner.write().unwrap_or_else(PoisonError::into_inner);
            let interner = guard
                .get_mut()
                .expect("Uninitialid cell after we initialized it");
            interner.intern(s)
        }
    }
}

/// A string interner
#[derive(Debug, Default)]
pub struct Interner {
    /// The storage for the underlying strings
    database: HashSet<&'static str>,
}
impl Interner {
    /// Create a new interner
    pub fn new() -> Self {
        Self::default()
    }

    /// Get an existing interned string, or return `None` if not interned
    pub fn get(&self, s: impl AsRef<str>) -> Option<&'static str> {
        self.database.get(s.as_ref()).copied()
    }

    /// Get an existing interned string, or intern it if not already interned
    pub fn intern(&mut self, s: impl AsRef<str>) -> &'static str {
        let s = s.as_ref();
        if let Some(s) = self.database.get(s) {
            s
        } else {
            self.database
                .insert(Box::leak(s.to_string().into_boxed_str()));
            self.database
                .get(s)
                .expect("Can't find something we just added")
        }
    }
}
