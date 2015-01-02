display :: Prelude.String -> SState a b c -> SState a b c
display label k ss@(Build_SSInfo sd _) =
    let f x = (unhandled x, active x, inactive x, handled x) in
    case IState.runIState k
             (trace (label GHC.Base.++ " - sd: "
                           GHC.Base.++ Prelude.show (f sd)) ss) of
        Prelude.Left e -> Prelude.error (Prelude.show e)
        x@(Prelude.Right (_, Build_SSInfo sd' _)) ->
            trace (label GHC.Base.++ " - sd': "
                         GHC.Base.++ Prelude.show (f sd')) x
