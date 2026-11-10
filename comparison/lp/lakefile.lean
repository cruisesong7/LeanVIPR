import Lake
open Lake DSL

/-! Comparison harness for `leanprover/lp`.

    The JSON backend rather than the FFI one: it carries no native dependencies and
    spawns a stock `soplex` binary at run time. See `../README.md`. -/

require LPVerify from git "https://github.com/leanprover/lp-verify" @
  "1131b0a11c683d4833cd735c83157a32952ad3aa"

require LPBackendSoplexJSON from git
  "https://github.com/leanprover/lp-backend-soplex-json" @
  "ce953f3b926815ebda5d65f88f1a06e9578abdc8"

package lpcompare

@[default_target] lean_lib LpCompare where
  roots := #[`LpCompare]
