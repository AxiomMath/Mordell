module

public meta import Lean

/-!
# The `faltings` tag attribute

Links a declaration to the label of the item (definition, lemma or theorem) of Bombieri's
*The Mordell conjecture revisited*, or of the background it uses, that the declaration
formalizes. It is written as the attribute name followed by the label as a string literal, on
the line above the declaration; an optional second string names one part of an enumerated
statement. The attribute has no effect on elaboration.

The syntax is deliberately not written out literally in this docstring, so that tools scanning
the sources for tags do not mistake an example for a real one.

## Reading the registrations

Every application adds the pair (declaration, label) to the persistent environment extension
`Faltings.faltingsTagExt`, so the registrations are stored in the `.olean` files and can be read
from an imported environment. `Faltings.faltingsTags` returns them all, imported ones first; the
command `#faltings_tags` prints them, one per line.
-/

public meta section

open Lean Elab Command

namespace Faltings

/-- The registrations of the `faltings` attribute: (declaration, label), in import order and
then in the order of application. -/
initialize faltingsTagExt : SimplePersistentEnvExtension (Name × String) (Array (Name × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

/-- Every (declaration, label) registration visible in `env`. -/
def faltingsTags (env : Environment) : Array (Name × String) :=
  faltingsTagExt.getState env

end Faltings

/-- Links a Lean declaration to a label: the attribute name, then the label in quotes,
optionally followed by a part in quotes. Not written literally here — see the module
docstring. -/
syntax (name := faltings) "faltings " str (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name  := `faltings
  descr := "marks a declaration as formalizing an item of the proof of the Mordell conjecture"
  applicationTime := .afterTypeChecking
  add   := fun decl stx kind => do
    unless kind == AttributeKind.global do
      throwError "the faltings attribute must be global"
    let label ← match stx with
      | `(attr| faltings $l:str $[$_part:str]?) => pure l.getString
      | _ => throwUnsupportedSyntax
    if label.isEmpty then
      throwError "the faltings attribute needs a non-empty label"
    modifyEnv (Faltings.faltingsTagExt.addEntry · (decl, label))
}

/-- Prints every `faltings` registration visible here, one `declaration ↦ label` per
line, imported ones first. -/
elab "#faltings_tags" : command => do
  let tags := Faltings.faltingsTags (← getEnv)
  if tags.isEmpty then
    logInfo "no faltings registrations"
  else
    logInfo <| m!"{tags.size} faltings registration(s):\n" ++
      MessageData.joinSep (tags.toList.map fun (d, l) => m!"{d} ↦ {l}") "\n"

end
