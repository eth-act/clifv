/-
Handwritten executable models of the `target-lexicon` 0.13.5 functions used by the extracted code,
transcribed from `target-lexicon-0.13.5/src/{triple,targets,parse_error}.rs` and the build-script
generated `host.rs` of the native x86_64-unknown-linux-gnu build (features: default `std` only,
so no `arch_zkasm`/`arch_z80`). The target-lexicon data types themselves are extracted.

`Triple::from_str` is the full parser (special cases, then architecture / vendor / operating
system / environment / binary format, with `default_binary_format`), working on the UTF-8 text
of the `&str`.

Formatting impls only write text; as in the Aeneas `core::fmt` model, a `Formatter` carries no
output, so they succeed and leave it unchanged.
-/
module
public import Aeneas
public import ClifvGen.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error clifv_extract_entry
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ClifvModels.TargetLexicon
open clifv_extract_entry.target_lexicon.targets clifv_extract_entry.target_lexicon.triple

deriving instance DecidableEq for target_lexicon.targets.ArmArchitecture,
  target_lexicon.targets.Aarch64Architecture, target_lexicon.targets.X86_32Architecture,
  target_lexicon.targets.Mips32Architecture, target_lexicon.targets.Mips64Architecture,
  target_lexicon.targets.Riscv32Architecture, target_lexicon.targets.Riscv64Architecture,
  target_lexicon.targets.CleverArchitecture

deriving instance DecidableEq for target_lexicon.targets.Architecture

/-- `OperatingSystem::is_like_darwin`. -/
def isLikeDarwin : OperatingSystem → Bool
  | .Darwin _ | .IOS _ | .MacOSX _ | .TvOS _ | .VisionOS _ | .WatchOS _ | .XROS _ => true
  | _ => false

/-- `Architecture::pointer_width`. -/
def archPointerWidth : Architecture → core.result.Result PointerWidth Unit
  | .Unknown => .Err ()
  | .Avr | .Msp430 => .Ok .U16
  | .Arm _ => .Ok .U32
  | .Aarch64 _ => .Ok .U64
  | .Asmjs | .Hexagon | .X86_32 _ | .Riscv32 _ | .Sparc | .Wasm32 | .M68k | .Mips32 _
  | .Pulley32 | .Pulley32be | .Powerpc | .XTensa => .Ok .U32
  | .AmdGcn | .Bpfeb | .Bpfel | .Powerpc64le | .Riscv64 _ | .X86_64 | .X86_64h | .Mips64 _
  | .Nvptx64 | .Pulley64 | .Pulley64be | .Powerpc64 | .S390x | .Sparc64 | .Sparcv9
  | .LoongArch64 | .Wasm64 | .Clever _ => .Ok .U64

/-- `default_binary_format(triple)`. -/
def defaultBinaryFormat (t : Triple) : BinaryFormat :=
  match t.operating_system with
  | .None_ => match t.environment with
    | .Eabi | .Eabihf => .Elf
    | _ => .Unknown
  | .Aix => .Xcoff
  | os =>
    if isLikeDarwin os then .Macho
    else match os with
    | .Windows => .Coff
    | .Nebulet | .Emscripten | .VxWorks | .Wasi | .Unknown =>
      match t.architecture with
      | .Wasm32 | .Wasm64 => .Wasm
      | .Unknown => .Unknown
      | _ => .Elf
    | _ => .Elf

def unknownTriple : Triple :=
  { architecture := .Unknown, vendor := .Unknown, operating_system := .Unknown,
    environment := .Unknown, binary_format := .Unknown }

def armFromStr : String → Option ArmArchitecture
  | "arm" => some .Arm | "armeb" => some .Armeb | "armv4" => some .Armv4
  | "armv4t" => some .Armv4t | "armv5t" => some .Armv5t | "armv5te" => some .Armv5te
  | "armv5tej" => some .Armv5tej | "armv6" => some .Armv6 | "armv6j" => some .Armv6j
  | "armv6k" => some .Armv6k | "armv6z" => some .Armv6z | "armv6kz" => some .Armv6kz
  | "armv6t2" => some .Armv6t2 | "armv6m" => some .Armv6m | "armv7" => some .Armv7
  | "armv7a" => some .Armv7a | "armv7k" => some .Armv7k | "armv7ve" => some .Armv7ve
  | "armv7m" => some .Armv7m | "armv7r" => some .Armv7r | "armv7s" => some .Armv7s
  | "armv8" => some .Armv8 | "armv8a" => some .Armv8a | "armv8.1a" => some .Armv8_1a
  | "armv8.2a" => some .Armv8_2a | "armv8.3a" => some .Armv8_3a
  | "armv8.4a" => some .Armv8_4a | "armv8.5a" => some .Armv8_5a
  | "armv8m.base" => some .Armv8mBase | "armv8m.main" => some .Armv8mMain
  | "armv8r" => some .Armv8r | "thumbeb" => some .Thumbeb | "thumbv4t" => some .Thumbv4t
  | "thumbv5te" => some .Thumbv5te | "thumbv6m" => some .Thumbv6m
  | "thumbv7a" => some .Thumbv7a | "thumbv7em" => some .Thumbv7em
  | "thumbv7m" => some .Thumbv7m | "thumbv7neon" => some .Thumbv7neon
  | "thumbv8m.base" => some .Thumbv8mBase | "thumbv8m.main" => some .Thumbv8mMain
  | "armebv7r" => some .Armebv7r
  | _ => none

def aarch64FromStr : String → Option Aarch64Architecture
  | "aarch64" => some .Aarch64 | "arm64" => some .Aarch64 | "aarch64_be" => some .Aarch64be
  | _ => none

def cleverFromStr : String → Option CleverArchitecture
  | "clever" => some .Clever | "clever1.0" => some .Clever1_0
  | _ => none

def riscv32FromStr : String → Option Riscv32Architecture
  | "riscv32" => some .Riscv32 | "riscv32gc" => some .Riscv32gc | "riscv32i" => some .Riscv32i
  | "riscv32im" => some .Riscv32im | "riscv32ima" => some .Riscv32ima
  | "riscv32imac" => some .Riscv32imac | "riscv32imafc" => some .Riscv32imafc
  | "riscv32imc" => some .Riscv32imc
  | _ => none

def riscv64FromStr : String → Option Riscv64Architecture
  | "riscv64" => some .Riscv64 | "riscv64gc" => some .Riscv64gc
  | "riscv64imac" => some .Riscv64imac | "riscv64a23" => some .Riscv64a23
  | _ => none

def x86_32FromStr : String → Option X86_32Architecture
  | "i386" => some .I386 | "i586" => some .I586 | "i686" => some .I686
  | _ => none

def mips32FromStr : String → Option Mips32Architecture
  | "mips" => some .Mips | "mipsel" => some .Mipsel | "mipsisa32r6" => some .Mipsisa32r6
  | "mipsisa32r6el" => some .Mipsisa32r6el
  | _ => none

def mips64FromStr : String → Option Mips64Architecture
  | "mips64" => some .Mips64 | "mips64el" => some .Mips64el
  | "mipsisa64r6" => some .Mipsisa64r6 | "mipsisa64r6el" => some .Mipsisa64r6el
  | _ => none

/-- `Architecture::from_str`. -/
def archFromStr (s : String) : Option Architecture :=
  match s with
  | "unknown" => some .Unknown | "amdgcn" => some .AmdGcn | "asmjs" => some .Asmjs
  | "avr" => some .Avr | "bpfeb" => some .Bpfeb | "bpfel" => some .Bpfel
  | "hexagon" => some .Hexagon | "loongarch64" => some .LoongArch64 | "m68k" => some .M68k
  | "msp430" => some .Msp430 | "nvptx64" => some .Nvptx64 | "pulley32" => some .Pulley32
  | "pulley64" => some .Pulley64 | "pulley32be" => some .Pulley32be
  | "pulley64be" => some .Pulley64be | "powerpc" => some .Powerpc
  | "powerpc64" => some .Powerpc64 | "powerpc64le" => some .Powerpc64le
  | "s390x" => some .S390x | "sparc" => some .Sparc | "sparc64" => some .Sparc64
  | "sparcv9" => some .Sparcv9 | "wasm32" => some .Wasm32 | "wasm64" => some .Wasm64
  | "x86_64" => some .X86_64 | "x86_64h" => some .X86_64h | "xtensa" => some .XTensa
  | _ =>
    match armFromStr s with
    | some a => some (.Arm a)
    | none => match aarch64FromStr s with
    | some a => some (.Aarch64 a)
    | none => match riscv32FromStr s with
    | some a => some (.Riscv32 a)
    | none => match riscv64FromStr s with
    | some a => some (.Riscv64 a)
    | none => match x86_32FromStr s with
    | some a => some (.X86_32 a)
    | none => match mips32FromStr s with
    | some a => some (.Mips32 a)
    | none => match mips64FromStr s with
    | some a => some (.Mips64 a)
    | none => match cleverFromStr s with
    | some a => some (.Clever a)
    | none => none

/-- `str::split(c)`, as a list of character lists. -/
def splitChars (c : Char) : List Char → List (List Char)
  | [] => [[]]
  | x :: xs =>
    let rest := splitChars c xs
    if x = c then [] :: rest
    else match rest with
      | r :: rs => (x :: r) :: rs
      | [] => [[x]]

/-- `<uN as FromStr>::from_str` (decimal; an optional leading `+`; no other sign; overflow is
an error), for `N = bits`. -/
def parseUnsigned (bits : Nat) (cs : List Char) : Option Nat :=
  let digits := match cs with
    | '+' :: rest => rest
    | _ => cs
  if digits.isEmpty then none
  else
    digits.foldl (fun acc c => do
      let n ← acc
      if c.isDigit then
        let n := n * 10 + (c.toNat - '0'.toNat)
        if n < 2 ^ bits then some n else none
      else none) (some 0)

/-- `parse_darwin(name)` on the text after the name: `None` if empty, else
`major[.minor[.patch]]` (`u16`, `u8`, `u8`; missing parts are 0; more parts is an error). -/
def parseDarwin (rest : List Char) : Option (Option DeploymentTarget) :=
  if rest.isEmpty then some none
  else
    match splitChars '.' rest with
    | parts =>
      if parts.length > 3 then none
      else do
        let major ← parseUnsigned 16 (parts.getD 0 [])
        let minor ← match parts[1]? with
          | some p => parseUnsigned 8 p
          | none => some 0
        let patch ← match parts[2]? with
          | some p => parseUnsigned 8 p
          | none => some 0
        if h : major < 2 ^ UScalarTy.U16.numBits ∧ minor < 2 ^ UScalarTy.U8.numBits ∧
            patch < 2 ^ UScalarTy.U8.numBits then
          some (some ⟨UScalar.ofNatCore major h.1, UScalar.ofNatCore minor h.2.1,
            UScalar.ofNatCore patch h.2.2⟩)
        else none

/-- `OperatingSystem::from_str`. -/
def osFromStr (s : String) : Option OperatingSystem :=
  let cs := s.toList
  let stripPre (p : String) : Option (List Char) :=
    if p.toList.isPrefixOf cs then some (cs.drop p.length) else none
  match stripPre "darwin" with
  | some r => (parseDarwin r).map OperatingSystem.Darwin
  | none => match stripPre "ios" with
  | some r => (parseDarwin r).map OperatingSystem.IOS
  | none => match stripPre "macosx" with
  | some r => (parseDarwin r).map OperatingSystem.MacOSX
  | none => match stripPre "tvos" with
  | some r => (parseDarwin r).map OperatingSystem.TvOS
  | none => match stripPre "visionos" with
  | some r => (parseDarwin r).map OperatingSystem.VisionOS
  | none => match stripPre "watchos" with
  | some r => (parseDarwin r).map OperatingSystem.WatchOS
  | none => match stripPre "xros" with
  | some r => (parseDarwin r).map OperatingSystem.XROS
  | none =>
    match s with
    | "unknown" => some .Unknown | "aix" => some .Aix | "amdhsa" => some .AmdHsa
    | "bitrig" => some .Bitrig | "cloudabi" => some .Cloudabi | "cuda" => some .Cuda
    | "cygwin" => some .Cygwin | "dragonfly" => some .Dragonfly
    | "emscripten" => some .Emscripten | "freebsd" => some .Freebsd
    | "fuchsia" => some .Fuchsia | "haiku" => some .Haiku | "hermit" => some .Hermit
    | "horizon" => some .Horizon | "hurd" => some .Hurd | "illumos" => some .Illumos
    | "l4re" => some .L4re | "linux" => some .Linux | "nebulet" => some .Nebulet
    | "netbsd" => some .Netbsd | "none" => some .None_ | "openbsd" => some .Openbsd
    | "psp" => some .Psp | "redox" => some .Redox | "solaris" => some .Solaris
    | "solid_asp3" => some .SolidAsp3 | "uefi" => some .Uefi | "vxworks" => some .VxWorks
    | "wasi" => some .Wasi | "wasip1" => some .WasiP1 | "wasip2" => some .WasiP2
    | "windows" => some .Windows | "espidf" => some .Espidf
    | _ => none

/-- `Environment::from_str`. -/
def envFromStr : String → Option Environment
  | "unknown" => some .Unknown | "amdgiz" => some .AmdGiz | "android" => some .Android
  | "androideabi" => some .Androideabi | "eabi" => some .Eabi | "eabihf" => some .Eabihf
  | "gnu" => some .Gnu | "gnuabi64" => some .Gnuabi64 | "gnueabi" => some .Gnueabi
  | "gnueabihf" => some .Gnueabihf | "gnuspe" => some .Gnuspe | "gnux32" => some .Gnux32
  | "gnu_ilp32" => some .GnuIlp32 | "gnullvm" => some .GnuLlvm
  | "hermitkernel" => some .HermitKernel | "hurdkernel" => some .HurdKernel
  | "linuxkernel" => some .LinuxKernel | "macabi" => some .Macabi | "musl" => some .Musl
  | "musleabi" => some .Musleabi | "musleabihf" => some .Musleabihf
  | "muslabi64" => some .Muslabi64 | "msvc" => some .Msvc | "newlib" => some .Newlib
  | "none" => some .None | "kernel" => some .Kernel | "uclibc" => some .Uclibc
  | "uclibceabi" => some .Uclibceabi | "uclibceabihf" => some .Uclibceabihf
  | "sgx" => some .Sgx | "sim" => some .Sim | "softfloat" => some .Softfloat
  | "spe" => some .Spe | "threads" => some .Threads | "ohos" => some .Ohos
  | _ => none

/-- `BinaryFormat::from_str`. -/
def binFmtFromStr : String → Option BinaryFormat
  | "unknown" => some .Unknown | "elf" => some .Elf | "coff" => some .Coff
  | "macho" => some .Macho | "wasm" => some .Wasm | "xcoff" => some .Xcoff
  | _ => none

/-- `Vendor::from_str` (a custom vendor: non-empty, not another component name, first char
ASCII lowercase, all chars in `[a-z0-9_.]`). -/
def vendorFromStr (s : String) : Option Vendor :=
  match s with
  | "unknown" => some .Unknown | "amd" => some .Amd | "apple" => some .Apple
  | "espressif" => some .Espressif | "experimental" => some .Experimental
  | "fortanix" => some .Fortanix | "ibm" => some .Ibm | "kmc" => some .Kmc
  | "nintendo" => some .Nintendo | "nvidia" => some .Nvidia | "pc" => some .Pc
  | "rumprun" => some .Rumprun | "sun" => some .Sun | "uwp" => some .Uwp | "wrs" => some .Wrs
  | custom =>
    let cs := custom.toList
    match cs with
    | [] => none
    | c0 :: _ =>
      if (archFromStr custom).isSome || (osFromStr custom).isSome
          || (envFromStr custom).isSome || (binFmtFromStr custom).isSome then none
      else if !(c0.isLower) then none
      else if cs.any (fun c => !(c.isLower || c.isDigit || c = '_' || c = '.')) then none
      else some (.Custom (.Owned custom))

/-- `Triple::special_case_from_str`. -/
def specialCase (s : String) : Option Triple :=
  match s with
  | "armv6k-nintendo-3ds" =>
    let t : Triple := ⟨.Arm .Armv6k, .Nintendo, .Horizon, .Newlib, .Unknown⟩
    some { t with binary_format := defaultBinaryFormat t }
  | "riscv32imc-esp-espidf" =>
    let t : Triple := ⟨.Riscv32 .Riscv32imc, .Espressif, .Espidf, .Newlib, .Unknown⟩
    some { t with binary_format := defaultBinaryFormat t }
  | _ => none

/-- `Triple::from_str` on the text `s`. -/
def tripleFromString (s : String) : core.result.Result Triple target_lexicon.parse_error.ParseError :=
  match specialCase s with
  | some t => .Ok t
  | none =>
    let parts := (splitChars '-' s.toList).map String.ofList
    -- `split` always yields a first part.
    let first := parts.headD ""
    let parts := parts.tail
    match archFromStr first with
    | none => .Err (.UnrecognizedArchitecture first)
    | some arch =>
      let result := { unknownTriple with architecture := arch }
      let (hasVendor, result, parts) := match parts with
        | p :: ps => match vendorFromStr p with
          | some v => (true, { result with vendor := v }, ps)
          | none => (false, result, parts)
        | [] => (false, result, parts)
      let (hasOs, result, parts) := match parts with
        | p :: ps => match osFromStr p with
          | some o => (true, { result with operating_system := o }, ps)
          | none => (false, result, parts)
        | [] => (false, result, parts)
      let (hasEnv, result, parts) := match parts with
        | p :: ps => match envFromStr p with
          | some e => (true, { result with environment := e }, ps)
          | none => (false, result, parts)
        | [] => (false, result, parts)
      let (hasBin, result, parts) := match parts with
        | p :: ps => match binFmtFromStr p with
          | some b => (true, { result with binary_format := b }, ps)
          | none => (false, result, parts)
        | [] => (false, result, parts)
      let result := if hasBin then result else { result with binary_format := defaultBinaryFormat result }
      match parts with
      | [] => .Ok result
      | p :: _ =>
        .Err (if !hasVendor && !hasOs && !hasEnv && !hasBin then .UnrecognizedVendor p
          else if !hasOs && !hasEnv && !hasBin then .UnrecognizedOperatingSystem p
          else if !hasEnv && !hasBin then .UnrecognizedEnvironment p
          else if !hasBin then .UnrecognizedBinaryFormat p
          else .UnrecognizedField p)

/-- The text of a `&str` (always valid UTF-8). -/
def strText (s : Str) : Option String :=
  String.fromUTF8? ⟨((Slice.val s).map fun b => UInt8.ofNat b.val).toArray⟩

end ClifvModels.TargetLexicon

open ClifvModels.TargetLexicon

/-- [target_lexicon::triple::{target_lexicon::triple::PointerWidth}::bits] -/
def target_lexicon.triple.PointerWidth.bits
  : target_lexicon.triple.PointerWidth → Result Std.U8 :=
  fun w => ok (match w with | .U16 => 16#u8 | .U32 => 32#u8 | .U64 => 64#u8)

/-- [target_lexicon::triple::{target_lexicon::triple::Triple}::pointer_width]: `U32` for the
`Gnux32`/`GnuIlp32` environments, else `Architecture::pointer_width`. -/
def target_lexicon.triple.Triple.pointer_width
  :
  target_lexicon.triple.Triple → Result (core.result.Result
    target_lexicon.triple.PointerWidth Unit) :=
  fun t => ok (match t.environment with
    | .Gnux32 | .GnuIlp32 => .Ok .U32
    | _ => archPointerWidth t.architecture)

/-- [target_lexicon::targets::{core::cmp::PartialEq<target_lexicon::targets::Architecture, target_lexicon::targets::Architecture>}::eq]:
derived structural equality. -/
def target_lexicon.targets.Architecture.Insts.CoreCmpPartialEqArchitecture.eq
  :
  target_lexicon.targets.Architecture → target_lexicon.targets.Architecture
    → Result Bool :=
  fun a b => ok (decide (a = b))

/-- [target_lexicon::triple::{target_lexicon::triple::Triple}::default_calling_convention] -/
def target_lexicon.triple.Triple.default_calling_convention
  :
  target_lexicon.triple.Triple → Result (core.result.Result
    target_lexicon.triple.CallingConvention Unit) :=
  fun t => ok (
    if isLikeDarwin t.operating_system then
      match t.architecture with
      | .Aarch64 _ => .Ok .AppleAarch64
      | _ => .Ok .SystemV
    else match t.operating_system with
    | .Aix | .Bitrig | .Cloudabi | .Dragonfly | .Freebsd | .Fuchsia | .Haiku | .Hermit | .Hurd
    | .L4re | .Linux | .Netbsd | .Openbsd | .Redox | .Solaris => .Ok .SystemV
    | .Windows => .Ok .WindowsFastcall
    | .Nebulet | .Emscripten | .Wasi | .Unknown =>
      match t.architecture with
      | .Wasm32 => .Ok .WasmBasicCAbi
      | _ => .Err ()
    | _ => .Err ())

/-- [target_lexicon::triple::{core::fmt::Debug<target_lexicon::triple::CallingConvention>}::fmt]:
derived (writes the variant name). -/
def target_lexicon.triple.CallingConvention.Insts.CoreFmtDebug.fmt
  :
  target_lexicon.triple.CallingConvention → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ f => ok (.Ok (), f)

/-- [target_lexicon::triple::{core::clone::Clone<target_lexicon::triple::Triple>}::clone]:
derived (a copy of the value). -/
def target_lexicon.triple.Triple.Insts.CoreCloneClone.clone
  : target_lexicon.triple.Triple → Result target_lexicon.triple.Triple :=
  fun t => ok t

/-- [target_lexicon::host::{target_lexicon::triple::Triple}::host]: the generated `host.rs` of
the native x86_64-unknown-linux-gnu build. -/
def target_lexicon.host.Triple.host : Result target_lexicon.triple.Triple :=
  ok { architecture := .X86_64, vendor := .Unknown, operating_system := .Linux,
       environment := .Gnu, binary_format := .Elf }

/-- [target_lexicon::triple::{core::str::traits::FromStr<target_lexicon::triple::Triple, target_lexicon::parse_error::ParseError>}::from_str] -/
def target_lexicon.triple.Triple.Insts.CoreStrTraitsFromStrParseError.from_str
  :
  Str → Result (core.result.Result target_lexicon.triple.Triple
    target_lexicon.parse_error.ParseError) :=
  fun s => match strText s with
    | some t => ok (tripleFromString t)
    | none => fail .panic

/-- [target_lexicon::parse_error::{core::fmt::Display<target_lexicon::parse_error::ParseError>}::fmt]:
`write!(fmt, "Unrecognized ...: {}", msg)`. -/
def target_lexicon.parse_error.ParseError.Insts.CoreFmtDisplay.fmt
  :
  target_lexicon.parse_error.ParseError → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun _ f => ok (.Ok (), f)
