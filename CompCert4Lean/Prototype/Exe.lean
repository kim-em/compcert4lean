import CompCert4Lean.Prototype.Main

/-! The `leanCompiler` executable. Its `main` lives here so that other packages
can import `CompCert4Lean.Prototype.Main` and define executables of their own. -/

def main (args : List String) : IO UInt32 := do
  try CompCert4Lean.Prototype.run args
  catch error =>
    (← IO.getStderr).putStrLn ("leanCompiler: " ++ error.toString)
    return 1
