import Lake
open Lake DSL

package «analysis_i» where
  -- No extra package-wide options needed; individual files each `import Mathlib`.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- Each chapter of exercises lives in a numerically-named folder (2, 3, ..., 11)
-- matching the corresponding chapter of Tao's *Analysis I*. None of the exercise
-- files import one another, so a single glob per chapter is enough to make every
-- file in it a build target. Folder names starting with a digit cannot be written
-- as a bare Lean identifier in `import` statements (hence the guillemets below),
-- but that only matters for *writing* an import — Lake itself discovers and builds
-- these modules from the filesystem path just fine.
@[default_target]
lean_lib «AnalysisI» where
  globs := #[
    .submodules `«2»,
    .submodules `«3»,
    .submodules `«4»,
    .submodules `«5»,
    .submodules `«6»,
    .submodules `«7»,
    .submodules `«8»,
    .submodules `«9»,
    .submodules `«10»,
    .submodules `«11»
  ]
