// MIT License

// Copyright (c) 2022 Gavin Gray

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

use std::cell::RefCell;

use super::rustc_interface::errors::{DiagInner, TRACK_DIAGNOSTIC, ErrCode};
use super::rustc_interface::hir::def_id::LocalDefId;
use super::rustc_interface::span::Span;

thread_local! {
    static ERROR_CODES: RefCell<Vec<ErrCode>> = RefCell::new(Vec::default());
    static CURRENT_BODY: RefCell<Option<LocalDefId>> = const { RefCell::new(None) };
}

fn track_diagnostic<R>(d: DiagInner, f: &mut dyn FnMut(DiagInner) -> R) -> R {
  ERROR_CODES.with(|diagnostics| {
    let mut diagnostics = diagnostics.borrow_mut();
    if let Some(err_code) = d.code {
      diagnostics.push(err_code);
    }
  });

  // We need to actually report the diagnostic with the
  // provided function. Otherwise, a `DelayedBugPanic`
  // will cause an ICE.
  (*f)(d)
}

// ------------------------------------------------
// Interface methods for fetching registered errors

/// This should be called before analysing a new crate.
pub fn initialize_error_tracking() {
  TRACK_DIAGNOSTIC.swap(&(track_diagnostic as _));
}

/// Initialize the error tracking for a given routine. It's recommended
/// to call this on start of every new analysis. In Aquascope, this would
/// be per-body analyzed.
pub fn track_body_error_codes(def_id: LocalDefId) {
  // Update the current LocalDefId
  CURRENT_BODY.with(|id| {
    let mut id = id.borrow_mut();
    let old_value = id.replace(def_id);
  });
  ERROR_CODES.with(|diagnostics| {
    let mut diagnostics = diagnostics.borrow_mut();
    // FIXME(gavinleroy): we should really be caching the diagnostics by
    // LocalDefId, meaning that we don't have to clean them after
    // each analysis. This also has the added benefic of caching
    // in case we ever reuse processes for server queries.
    diagnostics.clear();
  });
}

pub fn get_registered_errors() -> Vec<ErrCode> {
  ERROR_CODES.with(|diagnostics| diagnostics.borrow().clone())
}
