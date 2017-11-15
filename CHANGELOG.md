# CHANGELOG

## v0.2.0

New functions have been introduced to adopt a "standard" API that returns either `{:ok, value}` or {`:error, error}` where `error` is an `Exception`.  The bang functions raise the `error`.

In many cases the `error` will be a `KeyError` where its `key` field is set to the list of missing, unknwon, etc keys.

### 1. New Functions

Many new functions "shadow" old functions but support the new API.

Added `opts_canonical_keys/2` and `opts_canonical_keys!/2`. These do the same job as `opts_canon_keys/2` but unknown keys cause a `KeyError` to be returned or raised.

Added `canonical_keys/2/` and `canonical_keys!/2` to canonicalise multiple keys.  Does same job as `canon_keys` but returns a `KeyError`.

Added `canonical_key/2` and `canonical_key!/2` to canonicalise a single key.

Added `opts_crue_defstruct/2` and `opts_crue_defstruct!/2`. These do the same job as `opts_create_defstruct/2` but unknown keys in the defaults map cause `{:error, %KeyError{}}` to be returned.

### 2. Old Functions

It is intended to deprecate functions that can error but do not support the  standard API; they are now "frozen".

### 3. Bug Fixes

`opts_sort_keys/2` was incorrectly sorting the other (not sort) keys when following the sorted keys. They now follow the sorted keys in the order they appeared in the original `opts`.

## v0.1.0

A package of utility functions for managing `Keyword` options.



