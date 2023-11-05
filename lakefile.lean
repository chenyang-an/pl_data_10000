import Lake
open Lake DSL

package «pl_train_10000» {
  -- add package configuration options here
}

lean_lib «PlTrain10000» {
  -- add library configuration options here
}

@[default_target]
lean_exe «pl_train_10000» {
  root := `Main
}
