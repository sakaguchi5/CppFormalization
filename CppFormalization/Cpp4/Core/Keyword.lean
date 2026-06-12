/-!
# CppFormalization.Cpp4.Core.Keyword

Lexical keyword vocabulary for the current Cpp4 fragment.

This layer remains lexical.  Whether a control word such as `break`,
`continue`, or `return` is usable at a particular program point is a
`ControlContext` question, not a keyword question.
-/

namespace Cpp4

/-- Reserved C++-like keywords tracked by the current Cpp4 fragment. -/
inductive Keyword where
  | kw_bool
  | kw_break
  | kw_case
  | kw_continue
  | kw_default
  | kw_do
  | kw_else
  | kw_false
  | kw_for
  | kw_if
  | kw_int
  | kw_nullptr
  | kw_return
  | kw_switch
  | kw_true
  | kw_void
  | kw_while
  deriving DecidableEq, Repr

namespace Keyword

/-- Canonical spelling of a reserved keyword. -/
def spelling : Keyword → String
  | .kw_bool => "bool"
  | .kw_break => "break"
  | .kw_case => "case"
  | .kw_continue => "continue"
  | .kw_default => "default"
  | .kw_do => "do"
  | .kw_else => "else"
  | .kw_false => "false"
  | .kw_for => "for"
  | .kw_if => "if"
  | .kw_int => "int"
  | .kw_nullptr => "nullptr"
  | .kw_return => "return"
  | .kw_switch => "switch"
  | .kw_true => "true"
  | .kw_void => "void"
  | .kw_while => "while"

end Keyword

/-- All keyword spellings currently reserved by the fragment. -/
def reservedKeywordNames : List String :=
  [ "bool", "break", "case", "continue", "default", "do", "else", "false"
  , "for", "if", "int", "nullptr", "return", "switch", "true", "void"
  , "while" ]

/-- A raw identifier spelling is reserved when it is one of the tracked keywords. -/
def IsReservedIdent (x : String) : Prop :=
  x ∈ reservedKeywordNames

/-- User-defined identifiers are raw strings that are not reserved keywords. -/
def ValidUserIdent (x : String) : Prop :=
  ¬ IsReservedIdent x

end Cpp4
