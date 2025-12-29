import Lake
open Lake DSL

package lambdacalc

@[default_target]
lean_lib LambdaCalc

lean_exe lambdacalc_repl where
  root := `LambdaCalc.REPL
