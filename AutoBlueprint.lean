import AutoBlueprint.Basic

open Lean Elab Command

namespace AutoBlueprint

def getStream (fname : Option String) : IO IO.FS.Stream :=
  match fname with
  | some fname => do
    let handle ← IO.FS.Handle.mk fname IO.FS.Mode.write
    pure $ IO.FS.Stream.ofHandle handle
  | none => do
    let stream ← IO.getStdout
    pure stream

def runForDebugging (fname : Option String) : CommandElabM String := do
  let stream ← getStream fname
  let env ← getEnv
  let envData : EnvironmentData := {env := env}

  IO.println "All modules..."
  stream.putStrLn s!"There are {envData.modules.size} imported modules:"
  for n in envData.modules.toList.take 5 do
    stream.putStrLn s!"{n}"
  stream.putStrLn "..."
  stream.putStrLn ""

  IO.println "User defined modules..."
  stream.putStrLn s!"There are {envData.userModules.size} user defined modules:"
  for n in envData.userModules do
    stream.putStrLn s!"{n}"
  stream.putStrLn ""

  IO.println "Automatically created constants in user defined modules..."
  stream.putStrLn s!"{envData.autoConstansInUserModules.toList.length} of them are automatically generated: "
  for (n, _) in envData.autoConstansInUserModules do
    stream.putStrLn s!"{n}"
  stream.putStrLn ""

  IO.println "Explicit constants in user defined modules..."
  stream.putStrLn s!"{envData.nonautoConstants.toList.length} of them are explicitly created by the user: "
  for (n, _) in envData.nonautoConstants do
    stream.putStrLn s!"{n}"
  stream.putStrLn ""

  IO.println "First order dependencies..."
  stream.putStrLn "First order dependencies of explicit constants:"
  for (n, c) in envData.nonautoConstants do
    let typeDep := envData.firstOrderTypeDependencies c
    let valueDep := envData.firstOrderValueDependencies c
    stream.putStrLn s!"{n}"
    stream.putStrLn s!"Type dependecies: {typeDep.toList}"
    stream.putStrLn s!"Value dependencies: {valueDep.toList}"
  stream.putStrLn ""

  IO.println "Higher order dependencies..."
  stream.putStrLn "Higher order dependencies of explicit constants:"
  for (n, c) in envData.nonautoConstants do
    let typeDep := envData.typeDependenciesAsNameSet c
    let valueDep := envData.valueDependenciesAsNameSet c
    stream.putStrLn s!"{n}"
    stream.putStrLn s!"Type dependencies: {typeDep.toList}"
    stream.putStrLn s!"Value dependencies: {valueDep.toList}"
  stream.putStrLn ""


  return "Success!"


def createBlueprint (fname : Option String) : CommandElabM Unit := do
  let stream ← getStream fname
  let env ← getEnv
  let envData : EnvironmentData := {env := env}

  let latex := envData.summarize.map
    fun decl => "".intercalate $ decl.toLatex.map ToString.toString

  IO.println "Writing to file..."
  for text in latex do
    stream.putStr text
    stream.putStrLn ""
  IO.println "Done!"

end AutoBlueprint
