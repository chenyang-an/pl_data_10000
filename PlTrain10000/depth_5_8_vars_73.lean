variable (p0 p6 p5 p1 p4 : Prop)
theorem file73_41 : ((((((False ∧ False) → False) ∨ ((p4 ∨ False) → (p4 → False))) ∨ (((p1 ∧ False) → False) ∧ ((p5 → False) ∨ (p6 → p0)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∧ False) → False) ∨ ((p4 ∨ False) → (p4 → False))) ∨ (((p1 ∧ False) → False) ∧ ((p5 → False) ∨ (p6 → p0)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p7 p6 p1 p4 p3 p0 : Prop)
theorem file73_610 : ((((((p1 ∨ p0) → False) → ((p4 → False) → (True → False))) → (((p6 ∨ True) → (p0 → True)) ∨ ((p7 → False) → False))) ∧ ((((False ∧ p3) → (p6 → False)) → False) ∨ (((p6 → False) ∧ (p1 ∨ p6)) ∧ ((True ∨ p6) → False)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case inl assump_10 =>
      have assump_50 : ((False ∧ p3) → (p6 → False)) := by
        intro assump_15
        intro assump_16
        cases assump_15
        case intro assump_19 assump_20 =>
          apply False.elim assump_19
      let assump_14 := assump_10 assump_50
      apply False.elim assump_14
    case inr assump_11 =>
      cases assump_11
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          cases assump_29
          case inl assump_32 =>
            have assump_51 : (True ∨ p6) := by
              apply Or.inl
              apply True.intro
            let assump_38 := assump_27 assump_51
            apply False.elim assump_38
          case inr assump_33 =>
            have assump_52 : (True ∨ p6) := by
              apply Or.inl
              apply True.intro
            let assump_46 := assump_27 assump_52
            apply False.elim assump_46


variable (p0 p5 p3 p1 p4 p7 p2 p6 : Prop)
theorem file73_1937 : (((((p4 → p2) → False) ∧ ((p3 ∨ p0) → False)) ∨ (((p3 → p0) ∧ (p1 → p7)) ∨ ((True → False) → False))) → ((((p6 ∨ p5) ∧ (p6 → p7)) ∨ ((True → False) → (p7 ∧ p5))) ∨ (((p3 → True) → False) → ((p5 ∨ True) → (p1 ∧ False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply Or.inr
      intro assump_10
      apply And.intro
      have assump_59 : True := by
        apply True.intro
      let assump_13 := assump_10 assump_59
      apply False.elim assump_13
      have assump_60 : True := by
        apply True.intro
      let assump_19 := assump_10 assump_60
      apply False.elim assump_19
  case inr assump_3 =>
    cases assump_3
    case inl assump_23 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        apply Or.inl
        apply Or.inr
        intro assump_31
        apply And.intro
        have assump_61 : True := by
          apply True.intro
        let assump_34 := assump_31 assump_61
        apply False.elim assump_34
        have assump_62 : True := by
          apply True.intro
        let assump_40 := assump_31 assump_62
        apply False.elim assump_40
    case inr assump_24 =>
      apply Or.inl
      apply Or.inr
      intro assump_46
      apply And.intro
      have assump_63 : True := by
        apply True.intro
      let assump_49 := assump_46 assump_63
      apply False.elim assump_49
      have assump_64 : True := by
        apply True.intro
      let assump_55 := assump_46 assump_64
      apply False.elim assump_55


variable (p4 p7 p3 p5 p1 p0 p2 p6 : Prop)
theorem file73_3578 : (((((p3 → p6) → (p7 → p7)) ∨ ((True ∨ p5) ∧ (p3 ∨ p4))) ∨ (((False → False) ∨ (False → False)) → False)) ∨ ((((False → p6) ∨ (False ∨ p3)) ∧ ((p2 → p6) → (p1 ∧ p7))) ∨ (((p3 → p6) → (p0 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  exact assump_2


variable (p3 p1 p5 p2 p0 p7 p6 p4 : Prop)
theorem file73_3953 : (((((p6 ∨ p1) → False) ∨ ((p4 ∧ p7) ∧ (p0 ∨ p0))) ∨ (((False ∧ False) ∨ (p1 ∧ p0)) ∨ ((p5 → p6) → (p7 ∨ p2)))) → ((((p5 ∧ p6) ∧ (True → p3)) → ((p3 ∧ p6) ∨ (p0 ∨ p5))) ∨ (((p0 → p0) ∨ (p1 → p3)) → False))) := by
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      apply Or.inl
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply Or.inr
          apply Or.inr
          exact assump_15
    case inr assump_9 =>
      cases assump_9
      case intro assump_23 assump_24 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          cases assump_24
          case inl assump_31 =>
            apply Or.inl
            intro assump_35
            cases assump_35
            case intro assump_36 assump_37 =>
              cases assump_36
              case intro assump_38 assump_39 =>
                apply Or.inr
                apply Or.inl
                exact assump_31
          case inr assump_32 =>
            apply Or.inl
            intro assump_48
            cases assump_48
            case intro assump_49 assump_50 =>
              cases assump_49
              case intro assump_51 assump_52 =>
                apply Or.inr
                apply Or.inl
                exact assump_32
  case inr assump_7 =>
    cases assump_7
    case inl assump_59 =>
      cases assump_59
      case inl assump_61 =>
        cases assump_61
        case intro assump_63 assump_64 =>
          apply False.elim assump_63
      case inr assump_62 =>
        cases assump_62
        case intro assump_67 assump_68 =>
          apply Or.inl
          intro assump_73
          cases assump_73
          case intro assump_74 assump_75 =>
            cases assump_74
            case intro assump_76 assump_77 =>
              apply Or.inr
              apply Or.inl
              exact assump_68
    case inr assump_60 =>
      apply Or.inl
      intro assump_86
      cases assump_86
      case intro assump_87 assump_88 =>
        cases assump_87
        case intro assump_89 assump_90 =>
          apply Or.inr
          apply Or.inr
          exact assump_89


variable (p1 p0 p6 p3 p7 p4 p2 p5 : Prop)
theorem file73_6264 : (((((p1 → p6) → False) ∧ ((False ∧ True) ∨ (p3 → False))) ∧ (((p0 ∧ p0) → (False ∨ p4)) ∨ ((p2 → p4) ∨ (False → False)))) → ((((p1 ∨ p7) ∧ (p7 → p7)) ∨ ((p6 ∧ p2) → False)) ∨ (((p4 ∨ p2) ∨ (p0 ∧ False)) ∧ ((False ∨ p2) ∧ (p3 ∨ p5))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
      case inr assump_9 =>
        cases assump_3
        case inl assump_16 =>
          apply Or.inl
          apply Or.inr
          intro assump_20
          cases assump_20
          case intro assump_21 assump_22 =>
            have assump_81 : (p1 → p6) := by
              intro assump_32
              exact assump_21
            let assump_31 := assump_4 assump_81
            apply False.elim assump_31
        case inr assump_17 =>
          cases assump_17
          case inl assump_38 =>
            apply Or.inl
            apply Or.inr
            intro assump_42
            cases assump_42
            case intro assump_43 assump_44 =>
              have assump_82 : (p1 → p6) := by
                intro assump_55
                exact assump_43
              let assump_54 := assump_4 assump_82
              apply False.elim assump_54
          case inr assump_39 =>
            apply Or.inl
            apply Or.inr
            intro assump_63
            cases assump_63
            case intro assump_64 assump_65 =>
              have assump_83 : (p1 → p6) := by
                intro assump_75
                exact assump_64
              let assump_74 := assump_4 assump_83
              apply False.elim assump_74


variable (p2 p0 p5 p1 p3 p6 p4 p7 : Prop)
theorem file73_8086 : (((((p5 → False) ∨ (p6 → p3)) → False) → (((p0 → p0) → False) → ((False ∨ p4) → False))) → ((((p2 ∧ p2) ∨ (False → False)) ∨ ((p1 → False) ∧ (p7 → False))) ∨ (((p4 ∨ p2) → False) ∨ ((p0 ∧ p4) ∨ (p5 → p7))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_4
  apply False.elim assump_4


variable (p2 p7 p3 p0 : Prop)
theorem file73_8461 : ((((((True ∧ False) → (False ∧ p0)) ∧ ((p0 ∧ p0) ∧ (p2 ∨ p2))) → False) ∧ ((((p0 ∧ False) ∧ (p7 → p3)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((p0 ∧ False) ∧ (p7 → p3)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
    let assump_8 := assump_3 assump_21
    apply False.elim assump_8


variable (p6 p7 p3 p4 p5 : Prop)
theorem file73_9041 : (((((p6 → False) ∧ (p4 ∧ p6)) → False) ∨ (((p7 → p6) → False) → False)) ∨ ((((False → True) ∨ (p4 → p5)) → False) ∨ (((False ∧ p5) → (False → True)) ∧ ((p3 ∨ True) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_18 : p6 := by
        exact assump_7
      let assump_14 := assump_2 assump_18
      apply False.elim assump_14


variable (p7 p2 p5 p0 p3 p4 p1 : Prop)
theorem file73_9569 : (((((False ∧ p2) ∨ (p2 → p4)) ∨ ((True → p2) → False)) → (((p1 ∨ p7) ∧ (p7 ∨ p0)) ∧ ((p5 → p7) ∧ (p5 ∨ False)))) → ((((False ∨ False) ∧ (p7 → False)) → ((p4 → False) → (True → False))) ∧ (((p2 → p2) ∧ (p3 ∧ p5)) ∨ ((False → False) ∨ (p5 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      apply False.elim assump_11
    case inr assump_12 =>
      apply False.elim assump_12
  apply Or.inr
  apply Or.inl
  intro assump_22
  apply False.elim assump_22


variable (p2 p5 : Prop)
theorem file73_10225 : (((((p5 → False) ∧ (p2 ∧ False)) → False) → False) → False) := by
  intro assump_1
  have assump_19 : (((p5 → False) ∧ (p2 ∧ False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p5 p6 p4 p1 p7 p0 p3 : Prop)
theorem file73_10671 : (((((p6 ∨ p7) → (p5 → False)) ∧ ((False ∨ p5) ∧ (p4 ∨ True))) → (((p7 ∨ p7) → False) ∨ ((p1 → False) ∧ (p5 ∧ p3)))) ∨ ((((p0 → p0) ∨ (p1 ∨ p7)) ∨ ((p5 → p7) ∧ (p1 ∧ False))) → (((p6 → p6) → False) ∨ ((p4 ∨ p0) → (False → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply False.elim assump_8
      case inr assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply Or.inl
          intro assump_18
          cases assump_18
          case inl assump_19 =>
            have assump_64 : (p6 ∨ p7) := by
              apply Or.inr
              exact assump_19
            let assump_26 := assump_2 assump_64
            have assump_65 : p5 := by
              exact assump_9
            let assump_27 := assump_26 assump_65
            apply False.elim assump_27
          case inr assump_20 =>
            have assump_66 : (p6 ∨ p7) := by
              apply Or.inr
              exact assump_20
            let assump_36 := assump_2 assump_66
            have assump_67 : p5 := by
              exact assump_9
            let assump_37 := assump_36 assump_67
            apply False.elim assump_37
        case inr assump_15 =>
          apply Or.inl
          intro assump_43
          cases assump_43
          case inl assump_44 =>
            have assump_68 : (p6 ∨ p7) := by
              apply Or.inr
              exact assump_44
            let assump_50 := assump_2 assump_68
            have assump_69 : p5 := by
              exact assump_9
            let assump_51 := assump_50 assump_69
            apply False.elim assump_51
          case inr assump_45 =>
            have assump_70 : (p6 ∨ p7) := by
              apply Or.inr
              exact assump_45
            let assump_59 := assump_2 assump_70
            have assump_71 : p5 := by
              exact assump_9
            let assump_60 := assump_59 assump_71
            apply False.elim assump_60


variable (p6 p7 : Prop)
theorem file73_12785 : (((((False → False) → False) → ((p7 ∧ p6) → (True ∨ p7))) → False) → False) := by
  intro assump_1
  have assump_18 : (((False → False) → False) → ((p7 ∧ p6) → (True ∨ p7))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 : Prop)
theorem file73_13210 : (((((False → p0) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : (((False → p0) → False) → False) := by
    intro assump_5
    have assump_19 : (False → p0) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p6 p2 p1 p4 p0 : Prop)
theorem file73_13650 : ((((((False ∧ p6) ∧ (p2 → False)) ∧ ((p6 ∧ p1) ∧ (p3 → False))) → False) → ((((p1 ∨ True) → (True → False)) ∨ ((p0 → p0) → False)) ∧ (((p0 ∧ p3) ∨ (p4 ∧ True)) → ((p1 → p6) ∧ (p6 → True))))) → False) := by
  intro assump_1
  have assump_34 : ((((False ∧ p6) ∧ (p2 → False)) ∧ ((p6 ∧ p1) ∧ (p3 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
  let assump_4 := assump_1 assump_34
  let assump_14 := And.left assump_4
  cases assump_14
  case inl assump_16 =>
    have assump_35 : (p1 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_20 := assump_16 assump_35
    have assump_36 : True := by
      apply True.intro
    let assump_21 := assump_20 assump_36
    apply False.elim assump_21
  case inr assump_17 =>
    have assump_37 : (p0 → p0) := by
      intro assump_28
      exact assump_28
    let assump_27 := assump_17 assump_37
    apply False.elim assump_27


variable (p5 p6 : Prop)
theorem file73_14794 : (((((False ∧ p6) → (p5 → False)) ∨ ((p5 → False) → (p6 ∧ p5))) → False) → False) := by
  intro assump_1
  have assump_16 : (((False ∧ p6) → (p5 → False)) ∨ ((p5 → False) → (p6 ∧ p5))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p2 p6 p7 p4 p1 : Prop)
theorem file73_15249 : (((((p7 ∧ p4) ∨ (p7 ∨ p2)) → False) → (((False → False) ∨ (p1 → False)) → ((p7 → False) ∨ (p1 → False)))) ∨ ((((False → p1) ∧ (p4 → p6)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    have assump_29 : ((p7 ∧ p4) ∨ (p7 ∨ p2)) := by
      apply Or.inr
      apply Or.inl
      exact assump_9
    let assump_13 := assump_1 assump_29
    apply False.elim assump_13
  case inr assump_4 =>
    apply Or.inl
    intro assump_21
    have assump_30 : ((p7 ∧ p4) ∨ (p7 ∨ p2)) := by
      apply Or.inr
      apply Or.inl
      exact assump_21
    let assump_25 := assump_1 assump_30
    apply False.elim assump_25


variable (p1 p3 p0 p5 p2 : Prop)
theorem file73_16016 : ((((((p3 → False) → (p2 → False)) ∧ ((p0 → True) → (p2 → False))) → False) ∧ ((((p3 → False) ∧ (False ∨ p3)) → ((p5 ∧ p3) ∨ (p1 ∧ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_28 : (((p3 → False) ∧ (False ∨ p3)) → ((p5 ∧ p3) ∨ (p1 ∧ p5))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          apply False.elim assump_14
        case inr assump_15 =>
          have assump_29 : p3 := by
            exact assump_15
          let assump_21 := assump_10 assump_29
          apply False.elim assump_21
    let assump_8 := assump_3 assump_28
    apply False.elim assump_8


variable (p5 p3 p7 p4 : Prop)
theorem file73_16804 : (((((p3 ∨ p4) ∨ (p5 ∧ p7)) ∨ ((p3 → p5) ∧ (p4 → False))) → False) → False) := by
  intro assump_10
  have assump_33 : (((p3 ∨ p4) ∨ (p5 ∧ p7)) ∨ ((p3 → p5) ∧ (p4 → False))) := by
    apply Or.inr
    apply And.intro
    intro assump_14
    have assump_34 : (((p3 ∨ p4) ∨ (p5 ∧ p7)) ∨ ((p3 → p5) ∧ (p4 → False))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      exact assump_14
    let assump_18 := assump_10 assump_34
    apply False.elim assump_18
    intro assump_22
    have assump_35 : (((p3 ∨ p4) ∨ (p5 ∧ p7)) ∨ ((p3 → p5) ∧ (p4 → False))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      exact assump_22
    let assump_26 := assump_10 assump_35
    apply False.elim assump_26
  let assump_13 := assump_10 assump_33
  apply False.elim assump_13


variable (p7 p4 p2 p3 p0 p1 p5 : Prop)
theorem file73_17657 : (((((p7 ∨ True) ∧ (p4 ∧ False)) ∧ ((p0 → p4) ∨ (p5 → False))) → False) ∨ ((((p7 ∧ p7) → False) → ((False ∨ p2) → (p5 → False))) → (((p1 ∨ False) ∨ (p3 → p2)) → ((p4 ∧ p5) ∧ (True → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
      case inr assump_7 =>
        cases assump_5
        case intro assump_18 assump_19 =>
          apply False.elim assump_19


variable (p2 p1 p6 p4 : Prop)
theorem file73_18326 : (((((p1 → p1) ∧ (p2 ∨ p6)) ∨ ((p4 ∧ p1) ∧ (p6 ∧ p2))) → False) → ((((False → False) ∨ (p6 ∧ True)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_18 : ((False → False) ∨ (p6 ∧ True)) := by
    apply Or.inl
    intro assump_12
    apply False.elim assump_12
  let assump_11 := assump_2 assump_18
  apply False.elim assump_11


variable (p4 p0 p7 p1 p2 p5 p3 p6 : Prop)
theorem file73_18742 : ((((((p7 → p2) → (p0 → p2)) → False) → (((p6 → p6) → (True → False)) → False)) ∧ ((((p1 ∨ p4) → False) ∨ ((p5 ∨ p5) → (True → False))) ∧ (((p1 ∨ p4) ∧ (p1 → False)) ∧ ((True → False) ∨ (p3 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              cases assump_13
              case inl assump_22 =>
                have assump_98 : True := by
                  apply True.intro
                let assump_26 := assump_22 assump_98
                apply False.elim assump_26
              case inr assump_23 =>
                cases assump_23
                case intro assump_30 assump_31 =>
                  apply False.elim assump_31
            case inr assump_17 =>
              cases assump_13
              case inl assump_40 =>
                have assump_99 : True := by
                  apply True.intro
                let assump_44 := assump_40 assump_99
                apply False.elim assump_44
              case inr assump_41 =>
                cases assump_41
                case intro assump_48 assump_49 =>
                  apply False.elim assump_49
      case inr assump_9 =>
        cases assump_7
        case intro assump_56 assump_57 =>
          cases assump_56
          case intro assump_58 assump_59 =>
            cases assump_58
            case inl assump_60 =>
              cases assump_57
              case inl assump_66 =>
                have assump_100 : True := by
                  apply True.intro
                let assump_70 := assump_66 assump_100
                apply False.elim assump_70
              case inr assump_67 =>
                cases assump_67
                case intro assump_74 assump_75 =>
                  apply False.elim assump_75
            case inr assump_61 =>
              cases assump_57
              case inl assump_84 =>
                have assump_101 : True := by
                  apply True.intro
                let assump_88 := assump_84 assump_101
                apply False.elim assump_88
              case inr assump_85 =>
                cases assump_85
                case intro assump_92 assump_93 =>
                  apply False.elim assump_93


variable (p5 p7 p3 p1 p4 p0 : Prop)
theorem file73_21299 : (((((p3 → False) → (p0 → True)) → False) → False) ∨ ((((p1 → p4) → False) ∧ ((p7 ∨ p5) → (True → False))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_10 : ((p3 → False) → (p0 → True)) := by
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p6 p2 p5 p4 p0 : Prop)
theorem file73_21688 : ((((((p2 → False) ∧ (p0 ∧ p2)) → ((False ∨ p6) ∨ (p2 ∧ p4))) → (((p4 → False) → (False → p6)) → ((p4 → p5) → (False → False)))) → False) → False) := by
  intro assump_5
  have assump_18 : ((((p2 → False) ∧ (p0 ∧ p2)) → ((False ∨ p6) ∨ (p2 ∧ p4))) → (((p4 → False) → (False → p6)) → ((p4 → p5) → (False → False)))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    intro assump_12
    apply False.elim assump_12
  let assump_8 := assump_5 assump_18
  apply False.elim assump_8


variable (p3 p5 p0 p1 p4 p2 p7 : Prop)
theorem file73_22246 : ((((((True → False) → False) → ((False ∨ p2) ∧ (p3 ∨ p2))) → (((p1 ∧ p7) ∧ (False → p7)) ∨ ((p0 ∨ False) → (p7 → p1)))) ∧ ((((p5 → False) ∧ (p4 ∧ False)) → False) → False)) → False) := by
  intro assump_30
  cases assump_30
  case intro assump_31 assump_32 =>
    have assump_52 : (((p5 → False) ∧ (p4 ∧ False)) → False) := by
      intro assump_38
      cases assump_38
      case intro assump_39 assump_40 =>
        cases assump_40
        case intro assump_43 assump_44 =>
          apply False.elim assump_44
    let assump_37 := assump_32 assump_52
    apply False.elim assump_37


variable (p3 p7 p6 p2 p4 p0 : Prop)
theorem file73_22892 : (((((p6 ∧ p2) ∧ (p4 ∨ p7)) → ((True → False) → (p4 ∧ p2))) ∨ (((p2 ∨ False) → (p4 → False)) ∧ ((p3 ∨ p4) ∨ (p6 → True)))) ∧ ((((p4 → p3) ∧ (True → False)) → False) ∨ (((p3 ∧ p3) → False) ∧ ((True ∨ p0) → (p7 → True))))) := by
  apply And.intro
  apply Or.inl
  intro assump_11
  intro assump_12
  apply And.intro
  cases assump_11
  case intro assump_15 assump_16 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_16
      case inl assump_23 =>
        exact assump_23
      case inr assump_24 =>
        have assump_63 : True := by
          apply True.intro
        let assump_32 := assump_12 assump_63
        apply False.elim assump_32
  cases assump_11
  case intro assump_38 assump_39 =>
    cases assump_38
    case intro assump_40 assump_41 =>
      cases assump_39
      case inl assump_46 =>
        exact assump_41
      case inr assump_47 =>
        exact assump_41
  apply Or.inl
  intro assump_52
  cases assump_52
  case intro assump_53 assump_54 =>
    have assump_64 : True := by
      apply True.intro
    let assump_59 := assump_54 assump_64
    apply False.elim assump_59


variable (p7 p4 p0 p5 p3 p1 p6 p2 : Prop)
theorem file73_24080 : (((((False → False) ∨ (p1 → True)) → False) → (((p7 → False) → False) → ((p4 → p0) → (p6 ∧ p7)))) ∨ ((((p7 → False) ∨ (False → False)) ∨ ((p4 ∧ p5) ∧ (p5 ∧ p2))) ∧ (((p3 → p3) → (False ∧ p3)) → ((True → p1) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  have assump_30 : ((False → False) ∨ (p1 → True)) := by
    apply Or.inl
    intro assump_11
    apply False.elim assump_11
  let assump_10 := assump_1 assump_30
  apply False.elim assump_10
  have assump_31 : ((False → False) ∨ (p1 → True)) := by
    apply Or.inl
    intro assump_24
    apply False.elim assump_24
  let assump_23 := assump_1 assump_31
  apply False.elim assump_23


variable (p4 p3 p6 p0 : Prop)
theorem file73_24827 : (((((False → False) ∨ (p4 → p3)) → False) → (((p0 ∧ p4) ∨ (p4 ∧ p6)) ∧ ((p6 → p3) → False))) ∨ ((((p4 ∧ p4) ∨ (p4 ∨ False)) ∧ ((p6 ∧ True) → False)) → False)) := by
  apply Or.inl
  intro assump_5
  apply And.intro
  have assump_27 : ((False → False) ∨ (p4 → p3)) := by
    apply Or.inl
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_5 assump_27
  apply False.elim assump_8
  intro assump_15
  have assump_28 : ((False → False) ∨ (p4 → p3)) := by
    apply Or.inl
    intro assump_21
    apply False.elim assump_21
  let assump_20 := assump_5 assump_28
  apply False.elim assump_20


variable (p7 p1 p3 p6 p0 p4 p2 : Prop)
theorem file73_25499 : ((((((p6 ∧ p4) ∧ (p1 ∧ p6)) ∧ ((p2 ∧ False) ∧ (p7 → p3))) ∧ (((False ∨ p4) → (True ∧ False)) → False)) ∧ ((((p7 → False) → False) → ((p2 ∧ p1) → (True → p0))) → (((False ∨ p6) → False) ∧ ((False → False) ∧ (False ∨ p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_9
            case intro assump_16 assump_17 =>
              cases assump_7
              case intro assump_22 assump_23 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  apply False.elim assump_25


variable (p2 p7 p3 p5 p0 p1 p4 : Prop)
theorem file73_26391 : (((((p4 → False) → False) → ((p4 → True) ∨ (p1 → p1))) ∨ (((p3 → p5) → (p3 ∧ p2)) → False)) ∨ ((((p1 → p7) → (True ∨ p0)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply True.intro


variable (p2 p5 p7 p4 p6 p1 : Prop)
theorem file73_26696 : (((((True ∧ p2) → False) → ((p6 ∨ p7) ∨ (p4 ∧ p2))) ∨ (((p2 → True) → (False ∨ p5)) → ((True → True) ∧ (p6 ∧ p1)))) → ((((p7 → p6) → False) ∧ ((p4 → False) ∨ (p6 ∧ False))) → (((True ∧ False) → (False ∨ p7)) ∨ ((p1 → True) ∧ (p2 ∨ p7))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case inl assump_11 =>
        apply Or.inl
        intro assump_15
        cases assump_15
        case intro assump_16 assump_17 =>
          apply False.elim assump_17
      case inr assump_12 =>
        apply Or.inl
        intro assump_24
        cases assump_24
        case intro assump_25 assump_26 =>
          apply False.elim assump_26
    case inr assump_8 =>
      cases assump_8
      case intro assump_31 assump_32 =>
        apply False.elim assump_32


variable (p4 p6 p2 p0 p5 p1 p3 p7 : Prop)
theorem file73_27630 : ((((((p6 ∨ True) ∨ (p6 → False)) ∧ ((p7 ∨ p1) ∨ (p7 ∧ p2))) ∧ (((p5 ∨ False) ∧ (p5 → p0)) ∧ ((p4 → p5) → False))) ∧ ((((p7 → p2) → False) ∨ ((p0 → p3) ∨ (p1 ∨ p3))) ∧ (((p7 → False) ∧ (False ∧ p5)) ∧ ((p0 → False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_7
            case inl assump_14 =>
              cases assump_14
              case inl assump_16 =>
                cases assump_5
                case intro assump_20 assump_21 =>
                  cases assump_20
                  case intro assump_22 assump_23 =>
                    cases assump_22
                    case inl assump_24 =>
                      cases assump_3
                      case intro assump_32 assump_33 =>
                        cases assump_32
                        case inl assump_34 =>
                          cases assump_33
                          case intro assump_38 assump_39 =>
                            cases assump_38
                            case intro assump_40 assump_41 =>
                              cases assump_41
                              case intro assump_44 assump_45 =>
                                apply False.elim assump_44
                        case inr assump_35 =>
                          cases assump_35
                          case inl assump_48 =>
                            cases assump_33
                            case intro assump_52 assump_53 =>
                              cases assump_52
                              case intro assump_54 assump_55 =>
                                cases assump_55
                                case intro assump_58 assump_59 =>
                                  apply False.elim assump_58
                          case inr assump_49 =>
                            cases assump_49
                            case inl assump_62 =>
                              cases assump_33
                              case intro assump_66 assump_67 =>
                                cases assump_66
                                case intro assump_68 assump_69 =>
                                  cases assump_69
                                  case intro assump_72 assump_73 =>
                                    apply False.elim assump_72
                            case inr assump_63 =>
                              cases assump_33
                              case intro assump_78 assump_79 =>
                                cases assump_78
                                case intro assump_80 assump_81 =>
                                  cases assump_81
                                  case intro assump_84 assump_85 =>
                                    apply False.elim assump_84
                    case inr assump_25 =>
                      apply False.elim assump_25
              case inr assump_17 =>
                cases assump_5
                case intro assump_92 assump_93 =>
                  cases assump_92
                  case intro assump_94 assump_95 =>
                    cases assump_94
                    case inl assump_96 =>
                      cases assump_3
                      case intro assump_104 assump_105 =>
                        cases assump_104
                        case inl assump_106 =>
                          cases assump_105
                          case intro assump_110 assump_111 =>
                            cases assump_110
                            case intro assump_112 assump_113 =>
                              cases assump_113
                              case intro assump_116 assump_117 =>
                                apply False.elim assump_116
                        case inr assump_107 =>
                          cases assump_107
                          case inl assump_120 =>
                            cases assump_105
                            case intro assump_124 assump_125 =>
                              cases assump_124
                              case intro assump_126 assump_127 =>
                                cases assump_127
                                case intro assump_130 assump_131 =>
                                  apply False.elim assump_130
                          case inr assump_121 =>
                            cases assump_121
                            case inl assump_134 =>
                              cases assump_105
                              case intro assump_138 assump_139 =>
                                cases assump_138
                                case intro assump_140 assump_141 =>
                                  cases assump_141
                                  case intro assump_144 assump_145 =>
                                    apply False.elim assump_144
                            case inr assump_135 =>
                              cases assump_105
                              case intro assump_150 assump_151 =>
                                cases assump_150
                                case intro assump_152 assump_153 =>
                                  cases assump_153
                                  case intro assump_156 assump_157 =>
                                    apply False.elim assump_156
                    case inr assump_97 =>
                      apply False.elim assump_97
            case inr assump_15 =>
              cases assump_15
              case intro assump_162 assump_163 =>
                cases assump_5
                case intro assump_168 assump_169 =>
                  cases assump_168
                  case intro assump_170 assump_171 =>
                    cases assump_170
                    case inl assump_172 =>
                      cases assump_3
                      case intro assump_180 assump_181 =>
                        cases assump_180
                        case inl assump_182 =>
                          cases assump_181
                          case intro assump_186 assump_187 =>
                            cases assump_186
                            case intro assump_188 assump_189 =>
                              cases assump_189
                              case intro assump_192 assump_193 =>
                                apply False.elim assump_192
                        case inr assump_183 =>
                          cases assump_183
                          case inl assump_196 =>
                            cases assump_181
                            case intro assump_200 assump_201 =>
                              cases assump_200
                              case intro assump_202 assump_203 =>
                                cases assump_203
                                case intro assump_206 assump_207 =>
                                  apply False.elim assump_206
                          case inr assump_197 =>
                            cases assump_197
                            case inl assump_210 =>
                              cases assump_181
                              case intro assump_214 assump_215 =>
                                cases assump_214
                                case intro assump_216 assump_217 =>
                                  cases assump_217
                                  case intro assump_220 assump_221 =>
                                    apply False.elim assump_220
                            case inr assump_211 =>
                              cases assump_181
                              case intro assump_226 assump_227 =>
                                cases assump_226
                                case intro assump_228 assump_229 =>
                                  cases assump_229
                                  case intro assump_232 assump_233 =>
                                    apply False.elim assump_232
                    case inr assump_173 =>
                      apply False.elim assump_173
          case inr assump_11 =>
            cases assump_7
            case inl assump_240 =>
              cases assump_240
              case inl assump_242 =>
                cases assump_5
                case intro assump_246 assump_247 =>
                  cases assump_246
                  case intro assump_248 assump_249 =>
                    cases assump_248
                    case inl assump_250 =>
                      cases assump_3
                      case intro assump_258 assump_259 =>
                        cases assump_258
                        case inl assump_260 =>
                          cases assump_259
                          case intro assump_264 assump_265 =>
                            cases assump_264
                            case intro assump_266 assump_267 =>
                              cases assump_267
                              case intro assump_270 assump_271 =>
                                apply False.elim assump_270
                        case inr assump_261 =>
                          cases assump_261
                          case inl assump_274 =>
                            cases assump_259
                            case intro assump_278 assump_279 =>
                              cases assump_278
                              case intro assump_280 assump_281 =>
                                cases assump_281
                                case intro assump_284 assump_285 =>
                                  apply False.elim assump_284
                          case inr assump_275 =>
                            cases assump_275
                            case inl assump_288 =>
                              cases assump_259
                              case intro assump_292 assump_293 =>
                                cases assump_292
                                case intro assump_294 assump_295 =>
                                  cases assump_295
                                  case intro assump_298 assump_299 =>
                                    apply False.elim assump_298
                            case inr assump_289 =>
                              cases assump_259
                              case intro assump_304 assump_305 =>
                                cases assump_304
                                case intro assump_306 assump_307 =>
                                  cases assump_307
                                  case intro assump_310 assump_311 =>
                                    apply False.elim assump_310
                    case inr assump_251 =>
                      apply False.elim assump_251
              case inr assump_243 =>
                cases assump_5
                case intro assump_318 assump_319 =>
                  cases assump_318
                  case intro assump_320 assump_321 =>
                    cases assump_320
                    case inl assump_322 =>
                      cases assump_3
                      case intro assump_330 assump_331 =>
                        cases assump_330
                        case inl assump_332 =>
                          cases assump_331
                          case intro assump_336 assump_337 =>
                            cases assump_336
                            case intro assump_338 assump_339 =>
                              cases assump_339
                              case intro assump_342 assump_343 =>
                                apply False.elim assump_342
                        case inr assump_333 =>
                          cases assump_333
                          case inl assump_346 =>
                            cases assump_331
                            case intro assump_350 assump_351 =>
                              cases assump_350
                              case intro assump_352 assump_353 =>
                                cases assump_353
                                case intro assump_356 assump_357 =>
                                  apply False.elim assump_356
                          case inr assump_347 =>
                            cases assump_347
                            case inl assump_360 =>
                              cases assump_331
                              case intro assump_364 assump_365 =>
                                cases assump_364
                                case intro assump_366 assump_367 =>
                                  cases assump_367
                                  case intro assump_370 assump_371 =>
                                    apply False.elim assump_370
                            case inr assump_361 =>
                              cases assump_331
                              case intro assump_376 assump_377 =>
                                cases assump_376
                                case intro assump_378 assump_379 =>
                                  cases assump_379
                                  case intro assump_382 assump_383 =>
                                    apply False.elim assump_382
                    case inr assump_323 =>
                      apply False.elim assump_323
            case inr assump_241 =>
              cases assump_241
              case intro assump_388 assump_389 =>
                cases assump_5
                case intro assump_394 assump_395 =>
                  cases assump_394
                  case intro assump_396 assump_397 =>
                    cases assump_396
                    case inl assump_398 =>
                      cases assump_3
                      case intro assump_406 assump_407 =>
                        cases assump_406
                        case inl assump_408 =>
                          cases assump_407
                          case intro assump_412 assump_413 =>
                            cases assump_412
                            case intro assump_414 assump_415 =>
                              cases assump_415
                              case intro assump_418 assump_419 =>
                                apply False.elim assump_418
                        case inr assump_409 =>
                          cases assump_409
                          case inl assump_422 =>
                            cases assump_407
                            case intro assump_426 assump_427 =>
                              cases assump_426
                              case intro assump_428 assump_429 =>
                                cases assump_429
                                case intro assump_432 assump_433 =>
                                  apply False.elim assump_432
                          case inr assump_423 =>
                            cases assump_423
                            case inl assump_436 =>
                              cases assump_407
                              case intro assump_440 assump_441 =>
                                cases assump_440
                                case intro assump_442 assump_443 =>
                                  cases assump_443
                                  case intro assump_446 assump_447 =>
                                    apply False.elim assump_446
                            case inr assump_437 =>
                              cases assump_407
                              case intro assump_452 assump_453 =>
                                cases assump_452
                                case intro assump_454 assump_455 =>
                                  cases assump_455
                                  case intro assump_458 assump_459 =>
                                    apply False.elim assump_458
                    case inr assump_399 =>
                      apply False.elim assump_399
        case inr assump_9 =>
          cases assump_7
          case inl assump_466 =>
            cases assump_466
            case inl assump_468 =>
              cases assump_5
              case intro assump_472 assump_473 =>
                cases assump_472
                case intro assump_474 assump_475 =>
                  cases assump_474
                  case inl assump_476 =>
                    cases assump_3
                    case intro assump_484 assump_485 =>
                      cases assump_484
                      case inl assump_486 =>
                        cases assump_485
                        case intro assump_490 assump_491 =>
                          cases assump_490
                          case intro assump_492 assump_493 =>
                            cases assump_493
                            case intro assump_496 assump_497 =>
                              apply False.elim assump_496
                      case inr assump_487 =>
                        cases assump_487
                        case inl assump_500 =>
                          cases assump_485
                          case intro assump_504 assump_505 =>
                            cases assump_504
                            case intro assump_506 assump_507 =>
                              cases assump_507
                              case intro assump_510 assump_511 =>
                                apply False.elim assump_510
                        case inr assump_501 =>
                          cases assump_501
                          case inl assump_514 =>
                            cases assump_485
                            case intro assump_518 assump_519 =>
                              cases assump_518
                              case intro assump_520 assump_521 =>
                                cases assump_521
                                case intro assump_524 assump_525 =>
                                  apply False.elim assump_524
                          case inr assump_515 =>
                            cases assump_485
                            case intro assump_530 assump_531 =>
                              cases assump_530
                              case intro assump_532 assump_533 =>
                                cases assump_533
                                case intro assump_536 assump_537 =>
                                  apply False.elim assump_536
                  case inr assump_477 =>
                    apply False.elim assump_477
            case inr assump_469 =>
              cases assump_5
              case intro assump_544 assump_545 =>
                cases assump_544
                case intro assump_546 assump_547 =>
                  cases assump_546
                  case inl assump_548 =>
                    cases assump_3
                    case intro assump_556 assump_557 =>
                      cases assump_556
                      case inl assump_558 =>
                        cases assump_557
                        case intro assump_562 assump_563 =>
                          cases assump_562
                          case intro assump_564 assump_565 =>
                            cases assump_565
                            case intro assump_568 assump_569 =>
                              apply False.elim assump_568
                      case inr assump_559 =>
                        cases assump_559
                        case inl assump_572 =>
                          cases assump_557
                          case intro assump_576 assump_577 =>
                            cases assump_576
                            case intro assump_578 assump_579 =>
                              cases assump_579
                              case intro assump_582 assump_583 =>
                                apply False.elim assump_582
                        case inr assump_573 =>
                          cases assump_573
                          case inl assump_586 =>
                            cases assump_557
                            case intro assump_590 assump_591 =>
                              cases assump_590
                              case intro assump_592 assump_593 =>
                                cases assump_593
                                case intro assump_596 assump_597 =>
                                  apply False.elim assump_596
                          case inr assump_587 =>
                            cases assump_557
                            case intro assump_602 assump_603 =>
                              cases assump_602
                              case intro assump_604 assump_605 =>
                                cases assump_605
                                case intro assump_608 assump_609 =>
                                  apply False.elim assump_608
                  case inr assump_549 =>
                    apply False.elim assump_549
          case inr assump_467 =>
            cases assump_467
            case intro assump_614 assump_615 =>
              cases assump_5
              case intro assump_620 assump_621 =>
                cases assump_620
                case intro assump_622 assump_623 =>
                  cases assump_622
                  case inl assump_624 =>
                    cases assump_3
                    case intro assump_632 assump_633 =>
                      cases assump_632
                      case inl assump_634 =>
                        cases assump_633
                        case intro assump_638 assump_639 =>
                          cases assump_638
                          case intro assump_640 assump_641 =>
                            cases assump_641
                            case intro assump_644 assump_645 =>
                              apply False.elim assump_644
                      case inr assump_635 =>
                        cases assump_635
                        case inl assump_648 =>
                          cases assump_633
                          case intro assump_652 assump_653 =>
                            cases assump_652
                            case intro assump_654 assump_655 =>
                              cases assump_655
                              case intro assump_658 assump_659 =>
                                apply False.elim assump_658
                        case inr assump_649 =>
                          cases assump_649
                          case inl assump_662 =>
                            cases assump_633
                            case intro assump_666 assump_667 =>
                              cases assump_666
                              case intro assump_668 assump_669 =>
                                cases assump_669
                                case intro assump_672 assump_673 =>
                                  apply False.elim assump_672
                          case inr assump_663 =>
                            cases assump_633
                            case intro assump_678 assump_679 =>
                              cases assump_678
                              case intro assump_680 assump_681 =>
                                cases assump_681
                                case intro assump_684 assump_685 =>
                                  apply False.elim assump_684
                  case inr assump_625 =>
                    apply False.elim assump_625


variable (p5 p2 p6 p3 p0 p4 p1 : Prop)
theorem file73_51091 : (((((p3 ∨ p3) ∨ (True ∧ p4)) → ((p1 ∧ False) ∧ (p3 ∨ p6))) ∧ (((True → p3) → False) ∨ ((False → False) ∨ (p6 → False)))) → ((((p5 ∨ p2) ∨ (p6 ∨ p6)) ∧ ((p3 → False) ∧ (p0 → False))) → (((False → p2) ∧ (p1 ∧ True)) → ((p6 ∧ p3) ∨ (True ∨ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case intro assump_8 assump_9 =>
      cases assump_2
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_16
          case inl assump_18 =>
            cases assump_15
            case intro assump_22 assump_23 =>
              cases assump_1
              case intro assump_28 assump_29 =>
                cases assump_29
                case inl assump_32 =>
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                case inr assump_33 =>
                  cases assump_33
                  case inl assump_36 =>
                    apply Or.inr
                    apply Or.inl
                    apply True.intro
                  case inr assump_37 =>
                    apply Or.inr
                    apply Or.inl
                    apply True.intro
          case inr assump_19 =>
            cases assump_15
            case intro assump_44 assump_45 =>
              cases assump_1
              case intro assump_50 assump_51 =>
                cases assump_51
                case inl assump_54 =>
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                case inr assump_55 =>
                  cases assump_55
                  case inl assump_58 =>
                    apply Or.inr
                    apply Or.inl
                    apply True.intro
                  case inr assump_59 =>
                    apply Or.inr
                    apply Or.inl
                    apply True.intro
        case inr assump_17 =>
          cases assump_17
          case inl assump_64 =>
            cases assump_15
            case intro assump_68 assump_69 =>
              cases assump_1
              case intro assump_74 assump_75 =>
                cases assump_75
                case inl assump_78 =>
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                case inr assump_79 =>
                  cases assump_79
                  case inl assump_82 =>
                    apply Or.inr
                    apply Or.inl
                    apply True.intro
                  case inr assump_83 =>
                    apply Or.inr
                    apply Or.inl
                    apply True.intro
          case inr assump_65 =>
            cases assump_15
            case intro assump_90 assump_91 =>
              cases assump_1
              case intro assump_96 assump_97 =>
                cases assump_97
                case inl assump_100 =>
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                case inr assump_101 =>
                  cases assump_101
                  case inl assump_104 =>
                    apply Or.inr
                    apply Or.inl
                    apply True.intro
                  case inr assump_105 =>
                    apply Or.inr
                    apply Or.inl
                    apply True.intro


variable (p7 p5 p6 p2 p4 p0 p3 : Prop)
theorem file73_54598 : (((((False → False) ∧ (p7 ∧ p5)) ∧ ((p3 ∧ p0) → (True ∧ p4))) ∧ (((p6 ∧ p4) → False) ∧ ((p5 → False) ∧ (p2 ∧ p4)))) → False) := by
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          cases assump_8
          case intro assump_23 assump_24 =>
            cases assump_24
            case intro assump_27 assump_28 =>
              cases assump_28
              case intro assump_31 assump_32 =>
                have assump_43 : p5 := by
                  exact assump_16
                let assump_39 := assump_27 assump_43
                apply False.elim assump_39


variable (p2 p7 p1 p6 p0 p5 : Prop)
theorem file73_55433 : (((((True → False) → (p1 → p2)) → False) → (((p5 ∨ True) ∧ (True ∧ p6)) ∨ ((p0 ∧ True) ∨ (p6 → False)))) ∧ ((((False → True) → (True → False)) ∧ ((p7 → False) ∧ (p2 → p5))) → False)) := by
  apply And.intro
  intro assump_1
  apply Or.inr
  apply Or.inr
  intro assump_4
  have assump_41 : ((True → False) → (p1 → p2)) := by
    intro assump_9
    intro assump_10
    have assump_42 : True := by
      apply True.intro
    let assump_15 := assump_9 assump_42
    apply False.elim assump_15
  let assump_8 := assump_1 assump_41
  apply False.elim assump_8
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    cases assump_24
    case intro assump_27 assump_28 =>
      have assump_43 : (False → True) := by
        intro assump_36
        apply True.intro
      let assump_35 := assump_23 assump_43
      have assump_44 : True := by
        apply True.intro
      let assump_37 := assump_35 assump_44
      apply False.elim assump_37


variable (p2 p0 p5 p4 p7 p6 : Prop)
theorem file73_56449 : ((((((p4 ∧ p0) → False) ∨ ((p7 ∧ p4) → (p5 → p7))) → (((p5 → p6) → (True ∨ p2)) ∨ ((p0 → p5) ∧ (p7 → p5)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p4 ∧ p0) → False) ∨ ((p7 ∧ p4) → (p5 → p7))) → (((p5 → p6) → (True ∨ p2)) ∨ ((p0 → p5) ∧ (p7 → p5)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      intro assump_15
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p3 : Prop)
theorem file73_57093 : (((((p3 → False) ∧ (False ∧ False)) → False) → False) → False) := by
  intro assump_1
  have assump_17 : (((p3 → False) ∧ (False ∧ False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p5 p6 : Prop)
theorem file73_57530 : ((((((p6 → p5) → (p5 ∧ False)) ∧ ((False → False) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p6 → p5) → (p5 ∧ False)) ∧ ((False → False) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_23 : (False → False) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_7 assump_23
      apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p0 p7 p6 p3 p1 : Prop)
theorem file73_58107 : (((((p7 → True) ∨ (p6 ∨ p0)) ∨ ((p7 ∧ p3) ∨ (p1 ∧ p6))) → False) → False) := by
  intro assump_1
  have assump_9 : (((p7 → True) ∨ (p6 ∨ p0)) ∨ ((p7 ∧ p3) ∨ (p1 ∧ p6))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p5 p6 p2 p7 p4 p1 p3 : Prop)
theorem file73_58483 : (((((p3 ∨ False) → (p7 ∨ False)) → False) → False) → ((((p4 → p3) → (p3 → True)) ∨ ((p1 ∧ p2) → False)) ∨ (((p5 → p5) → (p5 ∨ p3)) → ((p6 ∨ p3) → (True ∨ p2))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  apply True.intro


variable (p0 p1 p4 p6 p2 p5 : Prop)
theorem file73_58811 : (((((p2 ∧ True) → False) ∧ ((p2 → False) ∨ (p0 → p6))) → (((p2 ∧ p0) ∧ (p4 ∧ p0)) → ((p4 → p0) → False))) ∨ ((((p2 → False) ∧ (p2 → False)) → ((True → False) → False)) → (((p5 ∨ p6) → (p4 ∨ p1)) ∨ ((p6 ∧ p5) → (p2 ∧ True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        cases assump_1
        case intro assump_20 assump_21 =>
          cases assump_21
          case inl assump_24 =>
            have assump_40 : p2 := by
              exact assump_8
            let assump_28 := assump_24 assump_40
            apply False.elim assump_28
          case inr assump_25 =>
            have assump_41 : (p2 ∧ True) := by
              apply And.intro
              exact assump_8
              apply True.intro
            let assump_36 := assump_20 assump_41
            apply False.elim assump_36


variable (p1 p3 p0 : Prop)
theorem file73_59862 : ((((((p1 ∧ p0) ∧ (True → False)) ∧ ((True → p3) ∨ (p1 → True))) → False) → False) → False) := by
  intro assump_1
  have assump_39 : ((((p1 ∧ p0) ∧ (True → False)) ∧ ((True → p3) ∨ (p1 → True))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case inl assump_18 =>
            have assump_40 : True := by
              apply True.intro
            let assump_24 := assump_9 assump_40
            apply False.elim assump_24
          case inr assump_19 =>
            have assump_41 : True := by
              apply True.intro
            let assump_32 := assump_9 assump_41
            apply False.elim assump_32
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p3 p0 p2 p7 p5 : Prop)
theorem file73_60797 : ((((((True ∧ True) → (p7 ∧ p0)) → ((p5 ∧ True) → (p5 ∨ p7))) ∨ (((p0 → p2) ∨ (p3 → False)) ∨ ((p7 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((True ∧ True) → (p7 ∧ p0)) → ((p5 ∧ True) → (p5 ∨ p7))) ∨ (((p0 → p2) ∨ (p3 → False)) ∨ ((p7 → False) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply Or.inl
      exact assump_7
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p1 p5 p0 p3 p7 p2 : Prop)
theorem file73_61375 : ((((((p6 → False) ∧ (False → p6)) → ((p0 → p1) → (p5 → False))) ∨ (((False ∧ p7) ∧ (p2 ∨ p0)) → False)) ∧ ((((p7 → False) ∨ (False → False)) ∨ ((p1 → False) → (p2 ∨ p2))) ∧ (((p3 → False) ∧ (p3 ∧ p2)) ∧ ((p6 ∨ p1) ∧ (p6 ∧ p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_9
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_19
                case intro assump_22 assump_23 =>
                  cases assump_17
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case inl assump_30 =>
                      cases assump_29
                      case intro assump_34 assump_35 =>
                        have assump_334 : p3 := by
                          exact assump_22
                        let assump_45 := assump_18 assump_334
                        apply False.elim assump_45
                    case inr assump_31 =>
                      cases assump_29
                      case intro assump_51 assump_52 =>
                        have assump_335 : p3 := by
                          exact assump_22
                        let assump_62 := assump_18 assump_335
                        apply False.elim assump_62
          case inr assump_13 =>
            cases assump_9
            case intro assump_68 assump_69 =>
              cases assump_68
              case intro assump_70 assump_71 =>
                cases assump_71
                case intro assump_74 assump_75 =>
                  cases assump_69
                  case intro assump_80 assump_81 =>
                    cases assump_80
                    case inl assump_82 =>
                      cases assump_81
                      case intro assump_86 assump_87 =>
                        have assump_336 : p3 := by
                          exact assump_74
                        let assump_97 := assump_70 assump_336
                        apply False.elim assump_97
                    case inr assump_83 =>
                      cases assump_81
                      case intro assump_103 assump_104 =>
                        have assump_337 : p3 := by
                          exact assump_74
                        let assump_114 := assump_70 assump_337
                        apply False.elim assump_114
        case inr assump_11 =>
          cases assump_9
          case intro assump_120 assump_121 =>
            cases assump_120
            case intro assump_122 assump_123 =>
              cases assump_123
              case intro assump_126 assump_127 =>
                cases assump_121
                case intro assump_132 assump_133 =>
                  cases assump_132
                  case inl assump_134 =>
                    cases assump_133
                    case intro assump_138 assump_139 =>
                      have assump_338 : p3 := by
                        exact assump_126
                      let assump_149 := assump_122 assump_338
                      apply False.elim assump_149
                  case inr assump_135 =>
                    cases assump_133
                    case intro assump_155 assump_156 =>
                      have assump_339 : p3 := by
                        exact assump_126
                      let assump_166 := assump_122 assump_339
                      apply False.elim assump_166
    case inr assump_5 =>
      cases assump_3
      case intro assump_172 assump_173 =>
        cases assump_172
        case inl assump_174 =>
          cases assump_174
          case inl assump_176 =>
            cases assump_173
            case intro assump_180 assump_181 =>
              cases assump_180
              case intro assump_182 assump_183 =>
                cases assump_183
                case intro assump_186 assump_187 =>
                  cases assump_181
                  case intro assump_192 assump_193 =>
                    cases assump_192
                    case inl assump_194 =>
                      cases assump_193
                      case intro assump_198 assump_199 =>
                        have assump_340 : p3 := by
                          exact assump_186
                        let assump_209 := assump_182 assump_340
                        apply False.elim assump_209
                    case inr assump_195 =>
                      cases assump_193
                      case intro assump_215 assump_216 =>
                        have assump_341 : p3 := by
                          exact assump_186
                        let assump_226 := assump_182 assump_341
                        apply False.elim assump_226
          case inr assump_177 =>
            cases assump_173
            case intro assump_232 assump_233 =>
              cases assump_232
              case intro assump_234 assump_235 =>
                cases assump_235
                case intro assump_238 assump_239 =>
                  cases assump_233
                  case intro assump_244 assump_245 =>
                    cases assump_244
                    case inl assump_246 =>
                      cases assump_245
                      case intro assump_250 assump_251 =>
                        have assump_342 : p3 := by
                          exact assump_238
                        let assump_261 := assump_234 assump_342
                        apply False.elim assump_261
                    case inr assump_247 =>
                      cases assump_245
                      case intro assump_267 assump_268 =>
                        have assump_343 : p3 := by
                          exact assump_238
                        let assump_278 := assump_234 assump_343
                        apply False.elim assump_278
        case inr assump_175 =>
          cases assump_173
          case intro assump_284 assump_285 =>
            cases assump_284
            case intro assump_286 assump_287 =>
              cases assump_287
              case intro assump_290 assump_291 =>
                cases assump_285
                case intro assump_296 assump_297 =>
                  cases assump_296
                  case inl assump_298 =>
                    cases assump_297
                    case intro assump_302 assump_303 =>
                      have assump_344 : p3 := by
                        exact assump_290
                      let assump_313 := assump_286 assump_344
                      apply False.elim assump_313
                  case inr assump_299 =>
                    cases assump_297
                    case intro assump_319 assump_320 =>
                      have assump_345 : p3 := by
                        exact assump_290
                      let assump_330 := assump_286 assump_345
                      apply False.elim assump_330


variable (p5 p7 p6 p1 p0 p3 : Prop)
theorem file73_68556 : (((((p1 → False) ∧ (False ∧ p6)) ∧ ((p0 → p5) ∧ (True ∧ p7))) ∧ (((p5 → p0) ∨ (p7 → False)) ∨ ((p1 ∧ p0) → (p5 ∧ p3)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply False.elim assump_10


variable (p4 p5 p3 p6 p7 p1 : Prop)
theorem file73_69035 : ((((((True ∧ True) → (p4 → p6)) ∨ ((p3 ∧ False) ∨ (True → p5))) → False) ∧ ((((True ∨ p5) ∧ (True → False)) ∨ ((True → False) ∨ (p6 ∧ p6))) ∧ (((p1 ∧ True) → (p4 → False)) ∧ ((True → p5) ∨ (p4 ∨ p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_7
            case intro assump_18 assump_19 =>
              cases assump_19
              case inl assump_22 =>
                have assump_200 : True := by
                  apply True.intro
                let assump_29 := assump_11 assump_200
                apply False.elim assump_29
              case inr assump_23 =>
                cases assump_23
                case inl assump_33 =>
                  have assump_201 : True := by
                    apply True.intro
                  let assump_39 := assump_11 assump_201
                  apply False.elim assump_39
                case inr assump_34 =>
                  have assump_202 : True := by
                    apply True.intro
                  let assump_47 := assump_11 assump_202
                  apply False.elim assump_47
          case inr assump_13 =>
            cases assump_7
            case intro assump_55 assump_56 =>
              cases assump_56
              case inl assump_59 =>
                have assump_203 : True := by
                  apply True.intro
                let assump_66 := assump_11 assump_203
                apply False.elim assump_66
              case inr assump_60 =>
                cases assump_60
                case inl assump_70 =>
                  have assump_204 : True := by
                    apply True.intro
                  let assump_76 := assump_11 assump_204
                  apply False.elim assump_76
                case inr assump_71 =>
                  have assump_205 : True := by
                    apply True.intro
                  let assump_84 := assump_11 assump_205
                  apply False.elim assump_84
      case inr assump_9 =>
        cases assump_9
        case inl assump_88 =>
          cases assump_7
          case intro assump_92 assump_93 =>
            cases assump_93
            case inl assump_96 =>
              have assump_206 : True := by
                apply True.intro
              let assump_103 := assump_88 assump_206
              apply False.elim assump_103
            case inr assump_97 =>
              cases assump_97
              case inl assump_107 =>
                have assump_207 : True := by
                  apply True.intro
                let assump_113 := assump_88 assump_207
                apply False.elim assump_113
              case inr assump_108 =>
                have assump_208 : True := by
                  apply True.intro
                let assump_121 := assump_88 assump_208
                apply False.elim assump_121
        case inr assump_89 =>
          cases assump_89
          case intro assump_125 assump_126 =>
            cases assump_7
            case intro assump_131 assump_132 =>
              cases assump_132
              case inl assump_135 =>
                have assump_209 : (((True ∧ True) → (p4 → p6)) ∨ ((p3 ∧ False) ∨ (True → p5))) := by
                  apply Or.inl
                  intro assump_145
                  intro assump_146
                  cases assump_145
                  case intro assump_149 assump_150 =>
                    exact assump_126
                let assump_144 := assump_2 assump_209
                apply False.elim assump_144
              case inr assump_136 =>
                cases assump_136
                case inl assump_158 =>
                  have assump_210 : (((True ∧ True) → (p4 → p6)) ∨ ((p3 ∧ False) ∨ (True → p5))) := by
                    apply Or.inl
                    intro assump_167
                    intro assump_168
                    cases assump_167
                    case intro assump_171 assump_172 =>
                      exact assump_126
                  let assump_166 := assump_2 assump_210
                  apply False.elim assump_166
                case inr assump_159 =>
                  have assump_211 : (((True ∧ True) → (p4 → p6)) ∨ ((p3 ∧ False) ∨ (True → p5))) := by
                    apply Or.inl
                    intro assump_187
                    intro assump_188
                    cases assump_187
                    case intro assump_191 assump_192 =>
                      exact assump_126
                  let assump_186 := assump_2 assump_211
                  apply False.elim assump_186


variable (p1 p3 p5 p4 : Prop)
theorem file73_73878 : ((((((p4 ∨ p5) ∧ (p1 → False)) → False) → (((p1 ∨ p3) ∧ (p3 → False)) → ((False → p5) ∨ (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p4 ∨ p5) ∧ (p1 → False)) → False) → (((p1 ∨ p3) ∧ (p3 → False)) → ((False → p5) ∨ (p1 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inl
        intro assump_17
        apply False.elim assump_17
      case inr assump_10 =>
        apply Or.inl
        intro assump_26
        apply False.elim assump_26
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p1 p0 p3 p7 p6 : Prop)
theorem file73_74601 : ((((((p3 ∨ p6) ∧ (p1 ∧ p7)) → ((p0 ∨ p6) ∨ (p7 → p3))) ∨ (((p6 → p1) → False) ∧ ((p6 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p3 ∨ p6) ∧ (p1 ∧ p7)) → ((p0 ∨ p6) ∨ (p7 → p3))) ∨ (((p6 → p1) → False) ∧ ((p6 ∧ False) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          apply Or.inr
          intro assump_18
          exact assump_8
      case inr assump_9 =>
        cases assump_7
        case intro assump_23 assump_24 =>
          apply Or.inl
          apply Or.inr
          exact assump_9
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p4 p3 p6 p7 p5 : Prop)
theorem file73_75438 : (((((False → False) ∨ (p5 ∨ p6)) ∧ ((p3 → p5) ∨ (p4 ∨ p7))) ∧ (((p7 ∨ p3) ∧ (p5 ∨ p6)) ∧ ((p7 → False) ∧ (p7 ∨ p7)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_9
        case inl assump_14 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              cases assump_20
              case inl assump_22 =>
                cases assump_21
                case inl assump_26 =>
                  cases assump_19
                  case intro assump_30 assump_31 =>
                    cases assump_31
                    case inl assump_34 =>
                      have assump_968 : p7 := by
                        exact assump_34
                      let assump_39 := assump_30 assump_968
                      apply False.elim assump_39
                    case inr assump_35 =>
                      have assump_969 : p7 := by
                        exact assump_35
                      let assump_46 := assump_30 assump_969
                      apply False.elim assump_46
                case inr assump_27 =>
                  cases assump_19
                  case intro assump_52 assump_53 =>
                    cases assump_53
                    case inl assump_56 =>
                      have assump_970 : p7 := by
                        exact assump_56
                      let assump_61 := assump_52 assump_970
                      apply False.elim assump_61
                    case inr assump_57 =>
                      have assump_971 : p7 := by
                        exact assump_57
                      let assump_68 := assump_52 assump_971
                      apply False.elim assump_68
              case inr assump_23 =>
                cases assump_21
                case inl assump_74 =>
                  cases assump_19
                  case intro assump_78 assump_79 =>
                    cases assump_79
                    case inl assump_82 =>
                      have assump_972 : p7 := by
                        exact assump_82
                      let assump_87 := assump_78 assump_972
                      apply False.elim assump_87
                    case inr assump_83 =>
                      have assump_973 : p7 := by
                        exact assump_83
                      let assump_94 := assump_78 assump_973
                      apply False.elim assump_94
                case inr assump_75 =>
                  cases assump_19
                  case intro assump_100 assump_101 =>
                    cases assump_101
                    case inl assump_104 =>
                      have assump_974 : p7 := by
                        exact assump_104
                      let assump_109 := assump_100 assump_974
                      apply False.elim assump_109
                    case inr assump_105 =>
                      have assump_975 : p7 := by
                        exact assump_105
                      let assump_116 := assump_100 assump_975
                      apply False.elim assump_116
        case inr assump_15 =>
          cases assump_15
          case inl assump_120 =>
            cases assump_7
            case intro assump_124 assump_125 =>
              cases assump_124
              case intro assump_126 assump_127 =>
                cases assump_126
                case inl assump_128 =>
                  cases assump_127
                  case inl assump_132 =>
                    cases assump_125
                    case intro assump_136 assump_137 =>
                      cases assump_137
                      case inl assump_140 =>
                        have assump_976 : p7 := by
                          exact assump_140
                        let assump_145 := assump_136 assump_976
                        apply False.elim assump_145
                      case inr assump_141 =>
                        have assump_977 : p7 := by
                          exact assump_141
                        let assump_152 := assump_136 assump_977
                        apply False.elim assump_152
                  case inr assump_133 =>
                    cases assump_125
                    case intro assump_158 assump_159 =>
                      cases assump_159
                      case inl assump_162 =>
                        have assump_978 : p7 := by
                          exact assump_162
                        let assump_167 := assump_158 assump_978
                        apply False.elim assump_167
                      case inr assump_163 =>
                        have assump_979 : p7 := by
                          exact assump_163
                        let assump_174 := assump_158 assump_979
                        apply False.elim assump_174
                case inr assump_129 =>
                  cases assump_127
                  case inl assump_180 =>
                    cases assump_125
                    case intro assump_184 assump_185 =>
                      cases assump_185
                      case inl assump_188 =>
                        have assump_980 : p7 := by
                          exact assump_188
                        let assump_193 := assump_184 assump_980
                        apply False.elim assump_193
                      case inr assump_189 =>
                        have assump_981 : p7 := by
                          exact assump_189
                        let assump_200 := assump_184 assump_981
                        apply False.elim assump_200
                  case inr assump_181 =>
                    cases assump_125
                    case intro assump_206 assump_207 =>
                      cases assump_207
                      case inl assump_210 =>
                        have assump_982 : p7 := by
                          exact assump_210
                        let assump_215 := assump_206 assump_982
                        apply False.elim assump_215
                      case inr assump_211 =>
                        have assump_983 : p7 := by
                          exact assump_211
                        let assump_222 := assump_206 assump_983
                        apply False.elim assump_222
          case inr assump_121 =>
            cases assump_7
            case intro assump_228 assump_229 =>
              cases assump_228
              case intro assump_230 assump_231 =>
                cases assump_230
                case inl assump_232 =>
                  cases assump_231
                  case inl assump_236 =>
                    cases assump_229
                    case intro assump_240 assump_241 =>
                      cases assump_241
                      case inl assump_244 =>
                        have assump_984 : p7 := by
                          exact assump_244
                        let assump_249 := assump_240 assump_984
                        apply False.elim assump_249
                      case inr assump_245 =>
                        have assump_985 : p7 := by
                          exact assump_245
                        let assump_256 := assump_240 assump_985
                        apply False.elim assump_256
                  case inr assump_237 =>
                    cases assump_229
                    case intro assump_262 assump_263 =>
                      cases assump_263
                      case inl assump_266 =>
                        have assump_986 : p7 := by
                          exact assump_266
                        let assump_271 := assump_262 assump_986
                        apply False.elim assump_271
                      case inr assump_267 =>
                        have assump_987 : p7 := by
                          exact assump_267
                        let assump_278 := assump_262 assump_987
                        apply False.elim assump_278
                case inr assump_233 =>
                  cases assump_231
                  case inl assump_284 =>
                    cases assump_229
                    case intro assump_288 assump_289 =>
                      cases assump_289
                      case inl assump_292 =>
                        have assump_988 : p7 := by
                          exact assump_292
                        let assump_297 := assump_288 assump_988
                        apply False.elim assump_297
                      case inr assump_293 =>
                        have assump_989 : p7 := by
                          exact assump_293
                        let assump_304 := assump_288 assump_989
                        apply False.elim assump_304
                  case inr assump_285 =>
                    cases assump_229
                    case intro assump_310 assump_311 =>
                      cases assump_311
                      case inl assump_314 =>
                        have assump_990 : p7 := by
                          exact assump_314
                        let assump_319 := assump_310 assump_990
                        apply False.elim assump_319
                      case inr assump_315 =>
                        have assump_991 : p7 := by
                          exact assump_315
                        let assump_326 := assump_310 assump_991
                        apply False.elim assump_326
      case inr assump_11 =>
        cases assump_11
        case inl assump_330 =>
          cases assump_9
          case inl assump_334 =>
            cases assump_7
            case intro assump_338 assump_339 =>
              cases assump_338
              case intro assump_340 assump_341 =>
                cases assump_340
                case inl assump_342 =>
                  cases assump_341
                  case inl assump_346 =>
                    cases assump_339
                    case intro assump_350 assump_351 =>
                      cases assump_351
                      case inl assump_354 =>
                        have assump_992 : p7 := by
                          exact assump_354
                        let assump_359 := assump_350 assump_992
                        apply False.elim assump_359
                      case inr assump_355 =>
                        have assump_993 : p7 := by
                          exact assump_355
                        let assump_366 := assump_350 assump_993
                        apply False.elim assump_366
                  case inr assump_347 =>
                    cases assump_339
                    case intro assump_372 assump_373 =>
                      cases assump_373
                      case inl assump_376 =>
                        have assump_994 : p7 := by
                          exact assump_376
                        let assump_381 := assump_372 assump_994
                        apply False.elim assump_381
                      case inr assump_377 =>
                        have assump_995 : p7 := by
                          exact assump_377
                        let assump_388 := assump_372 assump_995
                        apply False.elim assump_388
                case inr assump_343 =>
                  cases assump_341
                  case inl assump_394 =>
                    cases assump_339
                    case intro assump_398 assump_399 =>
                      cases assump_399
                      case inl assump_402 =>
                        have assump_996 : p7 := by
                          exact assump_402
                        let assump_407 := assump_398 assump_996
                        apply False.elim assump_407
                      case inr assump_403 =>
                        have assump_997 : p7 := by
                          exact assump_403
                        let assump_414 := assump_398 assump_997
                        apply False.elim assump_414
                  case inr assump_395 =>
                    cases assump_339
                    case intro assump_420 assump_421 =>
                      cases assump_421
                      case inl assump_424 =>
                        have assump_998 : p7 := by
                          exact assump_424
                        let assump_429 := assump_420 assump_998
                        apply False.elim assump_429
                      case inr assump_425 =>
                        have assump_999 : p7 := by
                          exact assump_425
                        let assump_436 := assump_420 assump_999
                        apply False.elim assump_436
          case inr assump_335 =>
            cases assump_335
            case inl assump_440 =>
              cases assump_7
              case intro assump_444 assump_445 =>
                cases assump_444
                case intro assump_446 assump_447 =>
                  cases assump_446
                  case inl assump_448 =>
                    cases assump_447
                    case inl assump_452 =>
                      cases assump_445
                      case intro assump_456 assump_457 =>
                        cases assump_457
                        case inl assump_460 =>
                          have assump_1000 : p7 := by
                            exact assump_460
                          let assump_465 := assump_456 assump_1000
                          apply False.elim assump_465
                        case inr assump_461 =>
                          have assump_1001 : p7 := by
                            exact assump_461
                          let assump_472 := assump_456 assump_1001
                          apply False.elim assump_472
                    case inr assump_453 =>
                      cases assump_445
                      case intro assump_478 assump_479 =>
                        cases assump_479
                        case inl assump_482 =>
                          have assump_1002 : p7 := by
                            exact assump_482
                          let assump_487 := assump_478 assump_1002
                          apply False.elim assump_487
                        case inr assump_483 =>
                          have assump_1003 : p7 := by
                            exact assump_483
                          let assump_494 := assump_478 assump_1003
                          apply False.elim assump_494
                  case inr assump_449 =>
                    cases assump_447
                    case inl assump_500 =>
                      cases assump_445
                      case intro assump_504 assump_505 =>
                        cases assump_505
                        case inl assump_508 =>
                          have assump_1004 : p7 := by
                            exact assump_508
                          let assump_513 := assump_504 assump_1004
                          apply False.elim assump_513
                        case inr assump_509 =>
                          have assump_1005 : p7 := by
                            exact assump_509
                          let assump_520 := assump_504 assump_1005
                          apply False.elim assump_520
                    case inr assump_501 =>
                      cases assump_445
                      case intro assump_526 assump_527 =>
                        cases assump_527
                        case inl assump_530 =>
                          have assump_1006 : p7 := by
                            exact assump_530
                          let assump_535 := assump_526 assump_1006
                          apply False.elim assump_535
                        case inr assump_531 =>
                          have assump_1007 : p7 := by
                            exact assump_531
                          let assump_542 := assump_526 assump_1007
                          apply False.elim assump_542
            case inr assump_441 =>
              cases assump_7
              case intro assump_548 assump_549 =>
                cases assump_548
                case intro assump_550 assump_551 =>
                  cases assump_550
                  case inl assump_552 =>
                    cases assump_551
                    case inl assump_556 =>
                      cases assump_549
                      case intro assump_560 assump_561 =>
                        cases assump_561
                        case inl assump_564 =>
                          have assump_1008 : p7 := by
                            exact assump_564
                          let assump_569 := assump_560 assump_1008
                          apply False.elim assump_569
                        case inr assump_565 =>
                          have assump_1009 : p7 := by
                            exact assump_565
                          let assump_576 := assump_560 assump_1009
                          apply False.elim assump_576
                    case inr assump_557 =>
                      cases assump_549
                      case intro assump_582 assump_583 =>
                        cases assump_583
                        case inl assump_586 =>
                          have assump_1010 : p7 := by
                            exact assump_586
                          let assump_591 := assump_582 assump_1010
                          apply False.elim assump_591
                        case inr assump_587 =>
                          have assump_1011 : p7 := by
                            exact assump_587
                          let assump_598 := assump_582 assump_1011
                          apply False.elim assump_598
                  case inr assump_553 =>
                    cases assump_551
                    case inl assump_604 =>
                      cases assump_549
                      case intro assump_608 assump_609 =>
                        cases assump_609
                        case inl assump_612 =>
                          have assump_1012 : p7 := by
                            exact assump_612
                          let assump_617 := assump_608 assump_1012
                          apply False.elim assump_617
                        case inr assump_613 =>
                          have assump_1013 : p7 := by
                            exact assump_613
                          let assump_624 := assump_608 assump_1013
                          apply False.elim assump_624
                    case inr assump_605 =>
                      cases assump_549
                      case intro assump_630 assump_631 =>
                        cases assump_631
                        case inl assump_634 =>
                          have assump_1014 : p7 := by
                            exact assump_634
                          let assump_639 := assump_630 assump_1014
                          apply False.elim assump_639
                        case inr assump_635 =>
                          have assump_1015 : p7 := by
                            exact assump_635
                          let assump_646 := assump_630 assump_1015
                          apply False.elim assump_646
        case inr assump_331 =>
          cases assump_9
          case inl assump_652 =>
            cases assump_7
            case intro assump_656 assump_657 =>
              cases assump_656
              case intro assump_658 assump_659 =>
                cases assump_658
                case inl assump_660 =>
                  cases assump_659
                  case inl assump_664 =>
                    cases assump_657
                    case intro assump_668 assump_669 =>
                      cases assump_669
                      case inl assump_672 =>
                        have assump_1016 : p7 := by
                          exact assump_672
                        let assump_677 := assump_668 assump_1016
                        apply False.elim assump_677
                      case inr assump_673 =>
                        have assump_1017 : p7 := by
                          exact assump_673
                        let assump_684 := assump_668 assump_1017
                        apply False.elim assump_684
                  case inr assump_665 =>
                    cases assump_657
                    case intro assump_690 assump_691 =>
                      cases assump_691
                      case inl assump_694 =>
                        have assump_1018 : p7 := by
                          exact assump_694
                        let assump_699 := assump_690 assump_1018
                        apply False.elim assump_699
                      case inr assump_695 =>
                        have assump_1019 : p7 := by
                          exact assump_695
                        let assump_706 := assump_690 assump_1019
                        apply False.elim assump_706
                case inr assump_661 =>
                  cases assump_659
                  case inl assump_712 =>
                    cases assump_657
                    case intro assump_716 assump_717 =>
                      cases assump_717
                      case inl assump_720 =>
                        have assump_1020 : p7 := by
                          exact assump_720
                        let assump_725 := assump_716 assump_1020
                        apply False.elim assump_725
                      case inr assump_721 =>
                        have assump_1021 : p7 := by
                          exact assump_721
                        let assump_732 := assump_716 assump_1021
                        apply False.elim assump_732
                  case inr assump_713 =>
                    cases assump_657
                    case intro assump_738 assump_739 =>
                      cases assump_739
                      case inl assump_742 =>
                        have assump_1022 : p7 := by
                          exact assump_742
                        let assump_747 := assump_738 assump_1022
                        apply False.elim assump_747
                      case inr assump_743 =>
                        have assump_1023 : p7 := by
                          exact assump_743
                        let assump_754 := assump_738 assump_1023
                        apply False.elim assump_754
          case inr assump_653 =>
            cases assump_653
            case inl assump_758 =>
              cases assump_7
              case intro assump_762 assump_763 =>
                cases assump_762
                case intro assump_764 assump_765 =>
                  cases assump_764
                  case inl assump_766 =>
                    cases assump_765
                    case inl assump_770 =>
                      cases assump_763
                      case intro assump_774 assump_775 =>
                        cases assump_775
                        case inl assump_778 =>
                          have assump_1024 : p7 := by
                            exact assump_778
                          let assump_783 := assump_774 assump_1024
                          apply False.elim assump_783
                        case inr assump_779 =>
                          have assump_1025 : p7 := by
                            exact assump_779
                          let assump_790 := assump_774 assump_1025
                          apply False.elim assump_790
                    case inr assump_771 =>
                      cases assump_763
                      case intro assump_796 assump_797 =>
                        cases assump_797
                        case inl assump_800 =>
                          have assump_1026 : p7 := by
                            exact assump_800
                          let assump_805 := assump_796 assump_1026
                          apply False.elim assump_805
                        case inr assump_801 =>
                          have assump_1027 : p7 := by
                            exact assump_801
                          let assump_812 := assump_796 assump_1027
                          apply False.elim assump_812
                  case inr assump_767 =>
                    cases assump_765
                    case inl assump_818 =>
                      cases assump_763
                      case intro assump_822 assump_823 =>
                        cases assump_823
                        case inl assump_826 =>
                          have assump_1028 : p7 := by
                            exact assump_826
                          let assump_831 := assump_822 assump_1028
                          apply False.elim assump_831
                        case inr assump_827 =>
                          have assump_1029 : p7 := by
                            exact assump_827
                          let assump_838 := assump_822 assump_1029
                          apply False.elim assump_838
                    case inr assump_819 =>
                      cases assump_763
                      case intro assump_844 assump_845 =>
                        cases assump_845
                        case inl assump_848 =>
                          have assump_1030 : p7 := by
                            exact assump_848
                          let assump_853 := assump_844 assump_1030
                          apply False.elim assump_853
                        case inr assump_849 =>
                          have assump_1031 : p7 := by
                            exact assump_849
                          let assump_860 := assump_844 assump_1031
                          apply False.elim assump_860
            case inr assump_759 =>
              cases assump_7
              case intro assump_866 assump_867 =>
                cases assump_866
                case intro assump_868 assump_869 =>
                  cases assump_868
                  case inl assump_870 =>
                    cases assump_869
                    case inl assump_874 =>
                      cases assump_867
                      case intro assump_878 assump_879 =>
                        cases assump_879
                        case inl assump_882 =>
                          have assump_1032 : p7 := by
                            exact assump_882
                          let assump_887 := assump_878 assump_1032
                          apply False.elim assump_887
                        case inr assump_883 =>
                          have assump_1033 : p7 := by
                            exact assump_883
                          let assump_894 := assump_878 assump_1033
                          apply False.elim assump_894
                    case inr assump_875 =>
                      cases assump_867
                      case intro assump_900 assump_901 =>
                        cases assump_901
                        case inl assump_904 =>
                          have assump_1034 : p7 := by
                            exact assump_904
                          let assump_909 := assump_900 assump_1034
                          apply False.elim assump_909
                        case inr assump_905 =>
                          have assump_1035 : p7 := by
                            exact assump_905
                          let assump_916 := assump_900 assump_1035
                          apply False.elim assump_916
                  case inr assump_871 =>
                    cases assump_869
                    case inl assump_922 =>
                      cases assump_867
                      case intro assump_926 assump_927 =>
                        cases assump_927
                        case inl assump_930 =>
                          have assump_1036 : p7 := by
                            exact assump_930
                          let assump_935 := assump_926 assump_1036
                          apply False.elim assump_935
                        case inr assump_931 =>
                          have assump_1037 : p7 := by
                            exact assump_931
                          let assump_942 := assump_926 assump_1037
                          apply False.elim assump_942
                    case inr assump_923 =>
                      cases assump_867
                      case intro assump_948 assump_949 =>
                        cases assump_949
                        case inl assump_952 =>
                          have assump_1038 : p7 := by
                            exact assump_952
                          let assump_957 := assump_948 assump_1038
                          apply False.elim assump_957
                        case inr assump_953 =>
                          have assump_1039 : p7 := by
                            exact assump_953
                          let assump_964 := assump_948 assump_1039
                          apply False.elim assump_964


variable (p0 p3 p2 p7 p1 p5 p4 : Prop)
theorem file73_104509 : ((((((p2 → p4) ∨ (p4 ∧ p5)) ∨ ((True ∨ p5) ∧ (p4 ∧ p1))) → (((True ∨ p3) ∨ (p7 → True)) → ((p1 ∨ p2) ∨ (p0 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_116 : ((((p2 → p4) ∨ (p4 ∧ p5)) ∨ ((True ∨ p5) ∧ (p4 ∧ p1))) → (((True ∨ p3) ∨ (p7 → True)) → ((p1 ∨ p2) ∨ (p0 ∨ True)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_5
        case inl assump_13 =>
          cases assump_13
          case inl assump_15 =>
            apply Or.inr
            apply Or.inr
            apply True.intro
          case inr assump_16 =>
            cases assump_16
            case intro assump_19 assump_20 =>
              apply Or.inr
              apply Or.inr
              apply True.intro
        case inr assump_14 =>
          cases assump_14
          case intro assump_25 assump_26 =>
            cases assump_25
            case inl assump_27 =>
              cases assump_26
              case intro assump_31 assump_32 =>
                apply Or.inl
                apply Or.inl
                exact assump_32
            case inr assump_28 =>
              cases assump_26
              case intro assump_39 assump_40 =>
                apply Or.inl
                apply Or.inl
                exact assump_40
      case inr assump_10 =>
        cases assump_5
        case inl assump_47 =>
          cases assump_47
          case inl assump_49 =>
            apply Or.inr
            apply Or.inr
            apply True.intro
          case inr assump_50 =>
            cases assump_50
            case intro assump_53 assump_54 =>
              apply Or.inr
              apply Or.inr
              apply True.intro
        case inr assump_48 =>
          cases assump_48
          case intro assump_59 assump_60 =>
            cases assump_59
            case inl assump_61 =>
              cases assump_60
              case intro assump_65 assump_66 =>
                apply Or.inl
                apply Or.inl
                exact assump_66
            case inr assump_62 =>
              cases assump_60
              case intro assump_73 assump_74 =>
                apply Or.inl
                apply Or.inl
                exact assump_74
    case inr assump_8 =>
      cases assump_5
      case inl assump_81 =>
        cases assump_81
        case inl assump_83 =>
          apply Or.inr
          apply Or.inr
          apply True.intro
        case inr assump_84 =>
          cases assump_84
          case intro assump_87 assump_88 =>
            apply Or.inr
            apply Or.inr
            apply True.intro
      case inr assump_82 =>
        cases assump_82
        case intro assump_93 assump_94 =>
          cases assump_93
          case inl assump_95 =>
            cases assump_94
            case intro assump_99 assump_100 =>
              apply Or.inl
              apply Or.inl
              exact assump_100
          case inr assump_96 =>
            cases assump_94
            case intro assump_107 assump_108 =>
              apply Or.inl
              apply Or.inl
              exact assump_108
  let assump_4 := assump_1 assump_116
  apply False.elim assump_4


variable (p1 p5 p2 p6 p0 p3 : Prop)
theorem file73_107805 : (((((p6 → p6) → (False ∧ p6)) → ((False → p6) ∨ (p6 → False))) ∨ (((p0 → False) → (p3 ∨ p2)) ∧ ((p5 ∧ p3) ∧ (p5 → False)))) ∨ ((((p5 → p6) → (p6 → p1)) → False) ∨ (((p0 ∨ p3) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p4 p6 p3 : Prop)
theorem file73_108164 : (((((p4 → p3) → False) → ((p3 → False) ∨ (False ∧ p6))) → False) → False) := by
  intro assump_1
  have assump_22 : (((p4 → p3) → False) → ((p3 → False) ∨ (False ∧ p6))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_23 : (p4 → p3) := by
      intro assump_13
      exact assump_8
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p5 p6 p0 p2 p7 p3 : Prop)
theorem file73_108671 : (((((p6 ∧ False) → (p2 ∨ p3)) ∨ ((p2 ∧ True) ∨ (p6 ∧ p5))) → False) → ((((p7 → False) → False) ∨ ((p0 ∧ False) ∨ (p5 → False))) → (((p2 → False) → False) ∨ ((p2 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    have assump_51 : (((p6 ∧ False) → (p2 ∨ p3)) ∨ ((p2 ∧ True) ∨ (p6 ∧ p5))) := by
      apply Or.inl
      intro assump_14
      cases assump_14
      case intro assump_15 assump_16 =>
        apply False.elim assump_16
    let assump_13 := assump_1 assump_51
    apply False.elim assump_13
  case inr assump_4 =>
    cases assump_4
    case inl assump_24 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        apply False.elim assump_27
    case inr assump_25 =>
      apply Or.inl
      intro assump_36
      have assump_52 : (((p6 ∧ False) → (p2 ∨ p3)) ∨ ((p2 ∧ True) ∨ (p6 ∧ p5))) := by
        apply Or.inl
        intro assump_41
        cases assump_41
        case intro assump_42 assump_43 =>
          apply False.elim assump_43
      let assump_40 := assump_1 assump_52
      apply False.elim assump_40


variable (p6 p3 p5 p2 p4 : Prop)
theorem file73_109860 : ((((((p3 → p5) → (p3 ∨ p3)) → ((p4 ∨ p6) → (True ∨ p2))) ∨ (((True → p2) → False) → ((True ∨ p6) → (True ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p3 → p5) → (p3 ∨ p3)) → ((p4 ∨ p6) → (True ∨ p2))) ∨ (((True → p2) → False) → ((True ∨ p6) → (True ∨ True)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply Or.inl
      apply True.intro
    case inr assump_8 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p5 p4 p6 p7 p3 p2 : Prop)
theorem file73_110489 : (((((p2 → False) ∧ (True → p5)) ∧ ((True ∨ p4) ∧ (p3 ∧ p7))) ∧ (((p6 → False) → (p3 ∨ p6)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_13
            case intro assump_18 assump_19 =>
              have assump_50 : ((p6 → False) → (p3 ∨ p6)) := by
                intro assump_27
                apply Or.inl
                exact assump_18
              let assump_26 := assump_3 assump_50
              apply False.elim assump_26
          case inr assump_15 =>
            cases assump_13
            case intro assump_35 assump_36 =>
              have assump_51 : ((p6 → False) → (p3 ∨ p6)) := by
                intro assump_44
                apply Or.inl
                exact assump_35
              let assump_43 := assump_3 assump_51
              apply False.elim assump_43


variable (p0 p3 p2 p4 p5 p1 : Prop)
theorem file73_111646 : ((((((p4 ∧ p1) → False) ∨ ((p1 → p3) ∧ (p5 → False))) → False) ∧ ((((p4 ∨ p2) ∧ (p5 ∧ p3)) → ((p1 ∧ p0) → (p5 ∧ p3))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_70 : (((p4 ∨ p2) ∧ (p5 ∧ p3)) → ((p1 ∧ p0) → (p5 ∧ p3))) := by
      intro assump_13
      intro assump_14
      apply And.intro
      cases assump_14
      case intro assump_15 assump_16 =>
        cases assump_13
        case intro assump_21 assump_22 =>
          cases assump_21
          case inl assump_23 =>
            cases assump_22
            case intro assump_27 assump_28 =>
              exact assump_27
          case inr assump_24 =>
            cases assump_22
            case intro assump_35 assump_36 =>
              exact assump_35
      cases assump_14
      case intro assump_41 assump_42 =>
        cases assump_13
        case intro assump_47 assump_48 =>
          cases assump_47
          case inl assump_49 =>
            cases assump_48
            case intro assump_53 assump_54 =>
              exact assump_54
          case inr assump_50 =>
            cases assump_48
            case intro assump_61 assump_62 =>
              exact assump_62
    let assump_12 := assump_7 assump_70
    apply False.elim assump_12


variable (p1 p2 p3 p5 p4 : Prop)
theorem file73_112982 : (((((True ∨ p4) ∨ (True → False)) → False) → (((p1 ∨ p5) ∨ (p4 → False)) ∧ ((True → False) → False))) ∨ ((((p3 → p1) → (p2 → False)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply Or.inr
  intro assump_4
  have assump_21 : ((True ∨ p4) ∨ (True → False)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_8 := assump_1 assump_21
  apply False.elim assump_8
  intro assump_12
  have assump_22 : ((True ∨ p4) ∨ (True → False)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_17 := assump_1 assump_22
  apply False.elim assump_17


variable (p7 p0 p4 p6 p2 p1 p3 : Prop)
theorem file73_113657 : (((((p1 → True) ∨ (False ∨ True)) ∨ ((p3 ∨ p1) → (False → p3))) ∨ (((p1 → False) ∧ (False ∨ p6)) → ((p3 ∨ p4) → (p7 ∨ p0)))) → ((((p4 → False) → False) ∧ ((p6 ∨ p3) ∧ (p7 → True))) → (((p2 → False) → (False → False)) ∨ ((p3 ∧ p6) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_1
        case inl assump_15 =>
          cases assump_15
          case inl assump_17 =>
            cases assump_17
            case inl assump_19 =>
              apply Or.inl
              intro assump_23
              intro assump_24
              apply False.elim assump_24
            case inr assump_20 =>
              cases assump_20
              case inl assump_27 =>
                apply False.elim assump_27
              case inr assump_28 =>
                apply Or.inl
                intro assump_33
                intro assump_34
                apply False.elim assump_34
          case inr assump_18 =>
            apply Or.inl
            intro assump_39
            intro assump_40
            apply False.elim assump_40
        case inr assump_16 =>
          apply Or.inl
          intro assump_45
          intro assump_46
          apply False.elim assump_46
      case inr assump_10 =>
        cases assump_1
        case inl assump_53 =>
          cases assump_53
          case inl assump_55 =>
            cases assump_55
            case inl assump_57 =>
              apply Or.inl
              intro assump_61
              intro assump_62
              apply False.elim assump_62
            case inr assump_58 =>
              cases assump_58
              case inl assump_65 =>
                apply False.elim assump_65
              case inr assump_66 =>
                apply Or.inl
                intro assump_71
                intro assump_72
                apply False.elim assump_72
          case inr assump_56 =>
            apply Or.inl
            intro assump_77
            intro assump_78
            apply False.elim assump_78
        case inr assump_54 =>
          apply Or.inl
          intro assump_83
          intro assump_84
          apply False.elim assump_84


variable (p3 p4 p2 : Prop)
theorem file73_115992 : (((((False ∧ p2) → (p3 → True)) ∨ ((p4 → False) → False)) → False) → False) := by
  intro assump_13
  have assump_22 : (((False ∧ p2) → (p3 → True)) ∨ ((p4 → False) → False)) := by
    apply Or.inl
    intro assump_17
    intro assump_18
    apply True.intro
  let assump_16 := assump_13 assump_22
  apply False.elim assump_16


variable (p7 p0 p5 p2 p1 p3 p4 p6 : Prop)
theorem file73_116385 : ((((((p4 → False) → (p6 → False)) ∨ ((p3 → p5) ∧ (p5 → p6))) ∧ (((p0 → False) → False) ∧ ((p1 ∧ False) ∧ (p3 ∧ p5)))) ∧ ((((p5 ∨ p2) → False) ∧ ((p6 → False) ∨ (False ∨ p3))) → (((p7 → False) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_17
      case inr assump_7 =>
        cases assump_7
        case intro assump_22 assump_23 =>
          cases assump_5
          case intro assump_28 assump_29 =>
            cases assump_29
            case intro assump_32 assump_33 =>
              cases assump_32
              case intro assump_34 assump_35 =>
                apply False.elim assump_35


variable (p7 p6 p5 p3 p4 p1 : Prop)
theorem file73_117449 : ((((((False ∨ p3) ∨ (p5 ∧ True)) ∧ ((p4 → False) ∧ (p7 ∧ p5))) ∨ (((True ∨ p1) ∨ (p1 → False)) ∨ ((p6 ∨ p6) ∨ (p3 → False)))) → False) → False) := by
  intro assump_15
  have assump_22 : ((((False ∨ p3) ∨ (p5 ∧ True)) ∧ ((p4 → False) ∧ (p7 ∧ p5))) ∨ (((True ∨ p1) ∨ (p1 → False)) ∨ ((p6 ∨ p6) ∨ (p3 → False)))) := by
    apply Or.inr
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_18 := assump_15 assump_22
  apply False.elim assump_18


variable (p1 p6 p7 p0 : Prop)
theorem file73_117977 : (((((False → p0) → False) → ((p1 → p6) → (p1 ∨ p7))) → False) → False) := by
  intro assump_1
  have assump_21 : (((False → p0) → False) → ((p1 → p6) → (p1 ∨ p7))) := by
    intro assump_5
    intro assump_6
    have assump_22 : (False → p0) := by
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_5 assump_22
    apply False.elim assump_11
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p0 p7 p4 p6 p1 p2 p5 p3 : Prop)
theorem file73_118482 : (((((p2 ∨ p6) ∧ (p3 → p0)) ∨ ((p5 ∨ p1) ∨ (p1 → False))) → False) → ((((p6 ∧ p5) → (p4 → p7)) → False) → False)) := by
  intro assump_49
  intro assump_50
  have assump_67 : (((p2 ∨ p6) ∧ (p3 → p0)) ∨ ((p5 ∨ p1) ∨ (p1 → False))) := by
    apply Or.inr
    apply Or.inr
    intro assump_56
    have assump_68 : (((p2 ∨ p6) ∧ (p3 → p0)) ∨ ((p5 ∨ p1) ∨ (p1 → False))) := by
      apply Or.inr
      apply Or.inl
      apply Or.inr
      exact assump_56
    let assump_60 := assump_49 assump_68
    apply False.elim assump_60
  let assump_55 := assump_49 assump_67
  apply False.elim assump_55


variable (p1 p7 p0 p5 p4 p3 p2 : Prop)
theorem file73_119135 : (((((p4 → p1) → (p4 ∨ False)) → ((p5 ∧ p7) → (p7 ∨ p2))) ∨ (((False ∧ p4) ∨ (p4 → False)) ∧ ((False → False) ∨ (p3 ∧ p5)))) ∨ ((((p1 → False) → (p7 → False)) ∨ ((p1 → False) ∨ (p3 → False))) → (((p3 → False) → False) → ((True ∧ p0) → (p3 ∧ p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inl
    exact assump_4


variable (p2 p1 p5 p4 : Prop)
theorem file73_119594 : (((((p1 ∨ True) → False) → ((p5 → False) → (p4 ∧ p2))) → False) → False) := by
  intro assump_1
  have assump_26 : (((p1 ∨ True) → False) → ((p5 → False) → (p4 ∧ p2))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    have assump_27 : (p1 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_11 := assump_5 assump_27
    apply False.elim assump_11
    have assump_28 : (p1 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_19 := assump_5 assump_28
    apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p6 p4 p5 p1 p7 : Prop)
theorem file73_120252 : (((((p5 ∧ p1) → (p4 ∧ p7)) ∧ ((p5 → p5) → False)) → False) ∨ ((((p7 ∨ True) → (p6 ∧ p1)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (p5 → p5) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p2 p6 p5 p7 p0 : Prop)
theorem file73_120654 : (((((p7 ∨ p5) ∧ (p6 ∧ p5)) ∨ ((p7 ∧ False) → (False ∧ p0))) → False) → ((((p6 ∧ p7) ∧ (True → False)) → ((p2 → False) → False)) → False)) := by
  intro assump_31
  intro assump_32
  have assump_54 : (((p7 ∨ p5) ∧ (p6 ∧ p5)) ∨ ((p7 ∧ False) → (False ∧ p0))) := by
    apply Or.inr
    intro assump_38
    apply And.intro
    cases assump_38
    case intro assump_39 assump_40 =>
      apply False.elim assump_40
    cases assump_38
    case intro assump_45 assump_46 =>
      apply False.elim assump_46
  let assump_37 := assump_31 assump_54
  apply False.elim assump_37


variable (p7 p6 p4 p0 : Prop)
theorem file73_121278 : (((((p0 → False) ∨ (p4 ∨ True)) → ((True ∨ p7) ∨ (p6 ∨ False))) → False) → False) := by
  intro assump_7
  have assump_25 : (((p0 → False) ∨ (p4 ∨ True)) → ((True ∨ p7) ∨ (p6 ∨ False))) := by
    intro assump_11
    cases assump_11
    case inl assump_12 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_13 =>
      cases assump_13
      case inl assump_16 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_17 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
  let assump_10 := assump_7 assump_25
  apply False.elim assump_10


variable (p7 p1 p4 p5 p2 p6 p0 : Prop)
theorem file73_121965 : (((((p6 ∨ p0) ∧ (p4 ∨ p7)) ∧ ((p5 ∧ False) ∧ (True → True))) ∧ (((p0 ∧ p6) ∨ (p2 → False)) → ((False → True) ∧ (p1 → p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_7
          case inl assump_12 =>
            cases assump_5
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                apply False.elim assump_19
          case inr assump_13 =>
            cases assump_5
            case intro assump_26 assump_27 =>
              cases assump_26
              case intro assump_28 assump_29 =>
                apply False.elim assump_29
        case inr assump_9 =>
          cases assump_7
          case inl assump_36 =>
            cases assump_5
            case intro assump_40 assump_41 =>
              cases assump_40
              case intro assump_42 assump_43 =>
                apply False.elim assump_43
          case inr assump_37 =>
            cases assump_5
            case intro assump_50 assump_51 =>
              cases assump_50
              case intro assump_52 assump_53 =>
                apply False.elim assump_53


variable (p7 p5 p4 p3 p0 p2 p1 p6 : Prop)
theorem file73_123387 : (((((p1 → False) → (p7 → p6)) → False) ∧ (((p2 → p7) ∧ (p4 → False)) ∧ ((p5 → p5) ∧ (p0 ∧ p6)))) → ((((True ∨ p3) ∧ (p0 → False)) ∧ ((p4 → False) → (False → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_20
              case intro assump_27 assump_28 =>
                cases assump_28
                case intro assump_31 assump_32 =>
                  have assump_95 : ((p1 → False) → (p7 → p6)) := by
                    intro assump_43
                    intro assump_44
                    exact assump_32
                  let assump_42 := assump_15 assump_95
                  apply False.elim assump_42
      case inr assump_8 =>
        cases assump_1
        case intro assump_58 assump_59 =>
          cases assump_59
          case intro assump_62 assump_63 =>
            cases assump_62
            case intro assump_64 assump_65 =>
              cases assump_63
              case intro assump_70 assump_71 =>
                cases assump_71
                case intro assump_74 assump_75 =>
                  have assump_96 : ((p1 → False) → (p7 → p6)) := by
                    intro assump_86
                    intro assump_87
                    exact assump_75
                  let assump_85 := assump_58 assump_96
                  apply False.elim assump_85


variable (p5 p6 p3 p4 p1 p0 p2 : Prop)
theorem file73_125137 : (((((p6 ∧ True) → (p6 ∨ False)) → False) → (((False → False) ∧ (p1 ∧ p0)) ∨ ((p0 ∧ p5) ∨ (p4 ∧ p5)))) ∧ ((((p2 ∧ p5) ∧ (p2 ∧ p0)) → ((p3 ∧ p3) ∨ (p0 ∧ False))) → (((True → False) ∨ (True → False)) → ((p6 → p6) → False)))) := by
  apply And.intro
  intro assump_5
  have assump_47 : ((p6 ∧ True) → (p6 ∨ False)) := by
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      apply Or.inl
      exact assump_13
  let assump_11 := assump_5 assump_47
  apply False.elim assump_11
  intro assump_22
  intro assump_23
  intro assump_24
  cases assump_23
  case inl assump_27 =>
    have assump_48 : True := by
      apply True.intro
    let assump_34 := assump_27 assump_48
    apply False.elim assump_34
  case inr assump_28 =>
    have assump_49 : True := by
      apply True.intro
    let assump_43 := assump_28 assump_49
    apply False.elim assump_43


variable (p0 p5 p7 p3 p2 p4 p6 p1 : Prop)
theorem file73_126080 : (((((p1 → False) → False) ∧ ((p3 ∨ p1) ∨ (p5 → False))) → (((False ∨ False) → (p2 ∨ True)) ∨ ((p0 → False) → False))) ∧ ((((p6 ∧ True) → (False ∧ p5)) ∧ ((p4 → False) ∧ (p3 ∧ p1))) → (((p1 → p1) ∧ (p1 ∨ p3)) ∨ ((p6 ∧ p7) ∧ (p3 → False))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        cases assump_12
        case inl assump_13 =>
          apply False.elim assump_13
        case inr assump_14 =>
          apply False.elim assump_14
      case inr assump_9 =>
        apply Or.inl
        intro assump_21
        cases assump_21
        case inl assump_22 =>
          apply False.elim assump_22
        case inr assump_23 =>
          apply False.elim assump_23
    case inr assump_7 =>
      apply Or.inl
      intro assump_30
      cases assump_30
      case inl assump_31 =>
        apply False.elim assump_31
      case inr assump_32 =>
        apply False.elim assump_32
  intro assump_37
  cases assump_37
  case intro assump_38 assump_39 =>
    cases assump_39
    case intro assump_42 assump_43 =>
      cases assump_43
      case intro assump_46 assump_47 =>
        apply Or.inl
        apply And.intro
        intro assump_52
        exact assump_52
        apply Or.inl
        exact assump_47


variable (p7 p5 p0 p2 p1 : Prop)
theorem file73_127538 : (((((True → p0) ∧ (False ∧ p1)) ∧ ((p0 ∨ p7) → (p0 → False))) → False) ∨ ((((p2 ∨ p2) ∨ (True ∧ p5)) → ((p5 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_17
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        apply False.elim assump_23


variable (p5 p1 p4 p3 p0 p2 p6 : Prop)
theorem file73_127986 : (((((p0 ∨ p1) → (False → True)) → False) → False) ∨ ((((p2 → p3) ∨ (p4 ∧ p5)) → False) ∧ (((p2 → p6) → False) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_10 : ((p0 ∨ p1) → (False → True)) := by
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p7 p1 p3 p5 p2 p0 p6 p4 : Prop)
theorem file73_128389 : ((((((p5 ∧ True) → False) ∧ ((p5 → p3) → (p3 ∨ p7))) → (((p0 ∨ p0) → False) ∧ ((p4 ∨ p5) → (p7 → False)))) ∧ ((((p1 → p0) → (p6 → False)) ∨ ((p7 ∨ p1) → False)) ∧ (((p4 ∨ True) ∧ (p7 ∧ p5)) ∧ ((p5 ∨ p2) → (p5 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              cases assump_15
              case intro assump_20 assump_21 =>
                have assump_86 : (p5 ∨ p2) := by
                  apply Or.inl
                  exact assump_21
                let assump_28 := assump_13 assump_86
                have assump_87 : p5 := by
                  exact assump_21
                let assump_29 := assump_28 assump_87
                apply False.elim assump_29
            case inr assump_17 =>
              cases assump_15
              case intro assump_35 assump_36 =>
                have assump_88 : (p5 ∨ p2) := by
                  apply Or.inl
                  exact assump_36
                let assump_43 := assump_13 assump_88
                have assump_89 : p5 := by
                  exact assump_36
                let assump_44 := assump_43 assump_89
                apply False.elim assump_44
      case inr assump_9 =>
        cases assump_7
        case intro assump_50 assump_51 =>
          cases assump_50
          case intro assump_52 assump_53 =>
            cases assump_52
            case inl assump_54 =>
              cases assump_53
              case intro assump_58 assump_59 =>
                have assump_90 : (p5 ∨ p2) := by
                  apply Or.inl
                  exact assump_59
                let assump_66 := assump_51 assump_90
                have assump_91 : p5 := by
                  exact assump_59
                let assump_67 := assump_66 assump_91
                apply False.elim assump_67
            case inr assump_55 =>
              cases assump_53
              case intro assump_73 assump_74 =>
                have assump_92 : (p5 ∨ p2) := by
                  apply Or.inl
                  exact assump_74
                let assump_81 := assump_51 assump_92
                have assump_93 : p5 := by
                  exact assump_74
                let assump_82 := assump_81 assump_93
                apply False.elim assump_82


variable (p4 p6 p3 p2 p1 p7 p0 : Prop)
theorem file73_131017 : (((((p0 → p7) ∨ (p0 ∨ p6)) ∧ ((p4 → False) ∨ (p3 → p3))) ∧ (((p1 ∨ p7) → (p4 ∨ p1)) ∧ ((p2 → p2) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            have assump_112 : (p2 → p2) := by
              intro assump_21
              exact assump_21
            let assump_20 := assump_15 assump_112
            apply False.elim assump_20
        case inr assump_11 =>
          cases assump_3
          case intro assump_29 assump_30 =>
            have assump_113 : (p2 → p2) := by
              intro assump_36
              exact assump_36
            let assump_35 := assump_30 assump_113
            apply False.elim assump_35
      case inr assump_7 =>
        cases assump_7
        case inl assump_42 =>
          cases assump_5
          case inl assump_46 =>
            cases assump_3
            case intro assump_50 assump_51 =>
              have assump_114 : (p2 → p2) := by
                intro assump_57
                exact assump_57
              let assump_56 := assump_51 assump_114
              apply False.elim assump_56
          case inr assump_47 =>
            cases assump_3
            case intro assump_65 assump_66 =>
              have assump_115 : (p2 → p2) := by
                intro assump_72
                exact assump_72
              let assump_71 := assump_66 assump_115
              apply False.elim assump_71
        case inr assump_43 =>
          cases assump_5
          case inl assump_80 =>
            cases assump_3
            case intro assump_84 assump_85 =>
              have assump_116 : (p2 → p2) := by
                intro assump_91
                exact assump_91
              let assump_90 := assump_85 assump_116
              apply False.elim assump_90
          case inr assump_81 =>
            cases assump_3
            case intro assump_99 assump_100 =>
              have assump_117 : (p2 → p2) := by
                intro assump_106
                exact assump_106
              let assump_105 := assump_100 assump_117
              apply False.elim assump_105


variable (p4 p3 p7 : Prop)
theorem file73_133379 : (((((False → False) → False) → False) → False) → ((((p4 ∨ p7) → (False → False)) → False) ∨ (((True → p3) ∨ (p7 → False)) → ((p3 ∧ True) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_22 : (((False → False) → False) → False) := by
    intro assump_9
    have assump_23 : (False → False) := by
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_9 assump_23
    apply False.elim assump_12
  let assump_8 := assump_1 assump_22
  apply False.elim assump_8


variable (p5 p4 p3 p0 p1 p2 p6 : Prop)
theorem file73_133960 : ((((((p3 ∨ p2) → (p5 ∨ p2)) ∧ ((False ∨ p1) → False)) ∧ (((p6 → False) ∧ (False → False)) ∧ ((p0 → False) ∧ (False → p6)))) ∧ ((((p4 → False) ∧ (False ∨ p4)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              have assump_48 : (((p4 → False) ∧ (False ∨ p4)) → False) := by
                intro assump_29
                cases assump_29
                case intro assump_30 assump_31 =>
                  cases assump_31
                  case inl assump_34 =>
                    apply False.elim assump_34
                  case inr assump_35 =>
                    have assump_49 : p4 := by
                      exact assump_35
                    let assump_41 := assump_30 assump_49
                    apply False.elim assump_41
              let assump_28 := assump_3 assump_48
              apply False.elim assump_28


variable (p1 p3 p7 p4 p0 p2 p6 : Prop)
theorem file73_135237 : (((((p4 ∧ p1) ∨ (False → False)) → False) → False) ∨ ((((p3 → False) ∨ (p4 → p0)) ∧ ((p6 ∧ p3) ∧ (p6 → p2))) ∨ (((p6 → p0) ∨ (p2 → False)) ∧ ((p7 → p1) ∧ (p0 ∨ p4))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p4 ∧ p1) ∨ (False → False)) := by
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p7 p1 p5 p0 p2 p4 p6 : Prop)
theorem file73_135695 : (((((True ∧ p4) → (False → p6)) → False) → False) ∨ ((((p3 → False) ∨ (False ∧ p2)) ∧ ((p0 → p7) → False)) → (((p3 ∧ False) ∧ (p1 ∨ p5)) ∨ ((p7 ∨ p7) ∨ (p5 → p0))))) := by
  apply Or.inl
  intro assump_1
  have assump_12 : ((True ∧ p4) → (False → p6)) := by
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p5 p2 p0 p1 p3 p6 : Prop)
theorem file73_136146 : (((((p2 ∨ p2) ∨ (p1 ∨ p0)) ∧ ((p2 ∧ p1) → False)) → (((False ∨ p2) → False) → ((p0 → p2) → False))) → ((((p5 → False) ∧ (False ∧ False)) → False) ∨ (((p3 → False) ∨ (False ∧ False)) → ((p5 → p6) ∧ (p1 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      apply False.elim assump_9


variable (p2 p5 p4 p1 p3 p7 p6 : Prop)
theorem file73_136617 : (((((False ∨ p3) → False) → False) → (((False ∨ p4) ∧ (False ∧ False)) → ((p3 → p5) → (p1 ∨ p7)))) ∨ ((((p4 → False) → False) ∧ ((False → False) ∨ (p5 ∨ True))) ∧ (((p3 → p6) ∧ (p6 → p2)) ∧ ((p6 → p6) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      apply False.elim assump_8
    case inr assump_9 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        apply False.elim assump_14


variable (p1 p0 p6 p4 p5 p2 p7 : Prop)
theorem file73_137213 : (((((False ∨ p2) → (True ∨ True)) → False) → False) ∨ ((((p7 → p7) → (p0 ∧ False)) → ((p0 ∧ p0) → (p1 → p6))) → (((p5 → p4) → False) → ((p7 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((False ∨ p2) → (True ∨ True)) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply False.elim assump_6
    case inr assump_7 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p1 p7 p3 p6 p2 p5 p4 : Prop)
theorem file73_137761 : ((((((p1 ∨ p7) ∨ (p7 ∨ False)) ∧ ((p0 ∨ p5) ∧ (True → False))) ∧ (((False ∨ p2) → False) ∨ ((True ∨ False) ∨ (p4 → p5)))) ∧ ((((False → p6) ∨ (p2 ∨ p6)) ∧ ((p3 ∧ True) ∨ (p3 ∧ p0))) ∨ (((p4 ∧ p7) ∨ (False → p3)) → ((False ∨ p4) → (p7 → p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_7
            case intro assump_14 assump_15 =>
              cases assump_14
              case inl assump_16 =>
                cases assump_5
                case inl assump_22 =>
                  cases assump_3
                  case inl assump_26 =>
                    cases assump_26
                    case intro assump_28 assump_29 =>
                      cases assump_28
                      case inl assump_30 =>
                        cases assump_29
                        case inl assump_34 =>
                          cases assump_34
                          case intro assump_36 assump_37 =>
                            have assump_2122 : True := by
                              apply True.intro
                            let assump_45 := assump_15 assump_2122
                            apply False.elim assump_45
                        case inr assump_35 =>
                          cases assump_35
                          case intro assump_49 assump_50 =>
                            have assump_2123 : True := by
                              apply True.intro
                            let assump_59 := assump_15 assump_2123
                            apply False.elim assump_59
                      case inr assump_31 =>
                        cases assump_31
                        case inl assump_63 =>
                          cases assump_29
                          case inl assump_67 =>
                            cases assump_67
                            case intro assump_69 assump_70 =>
                              have assump_2124 : (False ∨ p2) := by
                                apply Or.inr
                                exact assump_63
                              let assump_77 := assump_22 assump_2124
                              apply False.elim assump_77
                          case inr assump_68 =>
                            cases assump_68
                            case intro assump_81 assump_82 =>
                              have assump_2125 : (False ∨ p2) := by
                                apply Or.inr
                                exact assump_63
                              let assump_90 := assump_22 assump_2125
                              apply False.elim assump_90
                        case inr assump_64 =>
                          cases assump_29
                          case inl assump_96 =>
                            cases assump_96
                            case intro assump_98 assump_99 =>
                              have assump_2126 : True := by
                                apply True.intro
                              let assump_107 := assump_15 assump_2126
                              apply False.elim assump_107
                          case inr assump_97 =>
                            cases assump_97
                            case intro assump_111 assump_112 =>
                              have assump_2127 : True := by
                                apply True.intro
                              let assump_121 := assump_15 assump_2127
                              apply False.elim assump_121
                  case inr assump_27 =>
                    have assump_2128 : True := by
                      apply True.intro
                    let assump_133 := assump_15 assump_2128
                    apply False.elim assump_133
                case inr assump_23 =>
                  cases assump_23
                  case inl assump_137 =>
                    cases assump_137
                    case inl assump_139 =>
                      cases assump_3
                      case inl assump_143 =>
                        cases assump_143
                        case intro assump_145 assump_146 =>
                          cases assump_145
                          case inl assump_147 =>
                            cases assump_146
                            case inl assump_151 =>
                              cases assump_151
                              case intro assump_153 assump_154 =>
                                have assump_2129 : True := by
                                  apply True.intro
                                let assump_161 := assump_15 assump_2129
                                apply False.elim assump_161
                            case inr assump_152 =>
                              cases assump_152
                              case intro assump_165 assump_166 =>
                                have assump_2130 : True := by
                                  apply True.intro
                                let assump_174 := assump_15 assump_2130
                                apply False.elim assump_174
                          case inr assump_148 =>
                            cases assump_148
                            case inl assump_178 =>
                              cases assump_146
                              case inl assump_182 =>
                                cases assump_182
                                case intro assump_184 assump_185 =>
                                  have assump_2131 : True := by
                                    apply True.intro
                                  let assump_192 := assump_15 assump_2131
                                  apply False.elim assump_192
                              case inr assump_183 =>
                                cases assump_183
                                case intro assump_196 assump_197 =>
                                  have assump_2132 : True := by
                                    apply True.intro
                                  let assump_205 := assump_15 assump_2132
                                  apply False.elim assump_205
                            case inr assump_179 =>
                              cases assump_146
                              case inl assump_211 =>
                                cases assump_211
                                case intro assump_213 assump_214 =>
                                  have assump_2133 : True := by
                                    apply True.intro
                                  let assump_221 := assump_15 assump_2133
                                  apply False.elim assump_221
                              case inr assump_212 =>
                                cases assump_212
                                case intro assump_225 assump_226 =>
                                  have assump_2134 : True := by
                                    apply True.intro
                                  let assump_234 := assump_15 assump_2134
                                  apply False.elim assump_234
                      case inr assump_144 =>
                        have assump_2135 : True := by
                          apply True.intro
                        let assump_245 := assump_15 assump_2135
                        apply False.elim assump_245
                    case inr assump_140 =>
                      apply False.elim assump_140
                  case inr assump_138 =>
                    cases assump_3
                    case inl assump_253 =>
                      cases assump_253
                      case intro assump_255 assump_256 =>
                        cases assump_255
                        case inl assump_257 =>
                          cases assump_256
                          case inl assump_261 =>
                            cases assump_261
                            case intro assump_263 assump_264 =>
                              have assump_2136 : True := by
                                apply True.intro
                              let assump_272 := assump_15 assump_2136
                              apply False.elim assump_272
                          case inr assump_262 =>
                            cases assump_262
                            case intro assump_276 assump_277 =>
                              have assump_2137 : True := by
                                apply True.intro
                              let assump_286 := assump_15 assump_2137
                              apply False.elim assump_286
                        case inr assump_258 =>
                          cases assump_258
                          case inl assump_290 =>
                            cases assump_256
                            case inl assump_294 =>
                              cases assump_294
                              case intro assump_296 assump_297 =>
                                have assump_2138 : True := by
                                  apply True.intro
                                let assump_305 := assump_15 assump_2138
                                apply False.elim assump_305
                            case inr assump_295 =>
                              cases assump_295
                              case intro assump_309 assump_310 =>
                                have assump_2139 : True := by
                                  apply True.intro
                                let assump_319 := assump_15 assump_2139
                                apply False.elim assump_319
                          case inr assump_291 =>
                            cases assump_256
                            case inl assump_325 =>
                              cases assump_325
                              case intro assump_327 assump_328 =>
                                have assump_2140 : True := by
                                  apply True.intro
                                let assump_336 := assump_15 assump_2140
                                apply False.elim assump_336
                            case inr assump_326 =>
                              cases assump_326
                              case intro assump_340 assump_341 =>
                                have assump_2141 : True := by
                                  apply True.intro
                                let assump_350 := assump_15 assump_2141
                                apply False.elim assump_350
                    case inr assump_254 =>
                      have assump_2142 : True := by
                        apply True.intro
                      let assump_362 := assump_15 assump_2142
                      apply False.elim assump_362
              case inr assump_17 =>
                cases assump_5
                case inl assump_370 =>
                  cases assump_3
                  case inl assump_374 =>
                    cases assump_374
                    case intro assump_376 assump_377 =>
                      cases assump_376
                      case inl assump_378 =>
                        cases assump_377
                        case inl assump_382 =>
                          cases assump_382
                          case intro assump_384 assump_385 =>
                            have assump_2143 : True := by
                              apply True.intro
                            let assump_393 := assump_15 assump_2143
                            apply False.elim assump_393
                        case inr assump_383 =>
                          cases assump_383
                          case intro assump_397 assump_398 =>
                            have assump_2144 : True := by
                              apply True.intro
                            let assump_407 := assump_15 assump_2144
                            apply False.elim assump_407
                      case inr assump_379 =>
                        cases assump_379
                        case inl assump_411 =>
                          cases assump_377
                          case inl assump_415 =>
                            cases assump_415
                            case intro assump_417 assump_418 =>
                              have assump_2145 : (False ∨ p2) := by
                                apply Or.inr
                                exact assump_411
                              let assump_425 := assump_370 assump_2145
                              apply False.elim assump_425
                          case inr assump_416 =>
                            cases assump_416
                            case intro assump_429 assump_430 =>
                              have assump_2146 : (False ∨ p2) := by
                                apply Or.inr
                                exact assump_411
                              let assump_438 := assump_370 assump_2146
                              apply False.elim assump_438
                        case inr assump_412 =>
                          cases assump_377
                          case inl assump_444 =>
                            cases assump_444
                            case intro assump_446 assump_447 =>
                              have assump_2147 : True := by
                                apply True.intro
                              let assump_455 := assump_15 assump_2147
                              apply False.elim assump_455
                          case inr assump_445 =>
                            cases assump_445
                            case intro assump_459 assump_460 =>
                              have assump_2148 : True := by
                                apply True.intro
                              let assump_469 := assump_15 assump_2148
                              apply False.elim assump_469
                  case inr assump_375 =>
                    have assump_2149 : True := by
                      apply True.intro
                    let assump_481 := assump_15 assump_2149
                    apply False.elim assump_481
                case inr assump_371 =>
                  cases assump_371
                  case inl assump_485 =>
                    cases assump_485
                    case inl assump_487 =>
                      cases assump_3
                      case inl assump_491 =>
                        cases assump_491
                        case intro assump_493 assump_494 =>
                          cases assump_493
                          case inl assump_495 =>
                            cases assump_494
                            case inl assump_499 =>
                              cases assump_499
                              case intro assump_501 assump_502 =>
                                have assump_2150 : True := by
                                  apply True.intro
                                let assump_509 := assump_15 assump_2150
                                apply False.elim assump_509
                            case inr assump_500 =>
                              cases assump_500
                              case intro assump_513 assump_514 =>
                                have assump_2151 : True := by
                                  apply True.intro
                                let assump_522 := assump_15 assump_2151
                                apply False.elim assump_522
                          case inr assump_496 =>
                            cases assump_496
                            case inl assump_526 =>
                              cases assump_494
                              case inl assump_530 =>
                                cases assump_530
                                case intro assump_532 assump_533 =>
                                  have assump_2152 : True := by
                                    apply True.intro
                                  let assump_540 := assump_15 assump_2152
                                  apply False.elim assump_540
                              case inr assump_531 =>
                                cases assump_531
                                case intro assump_544 assump_545 =>
                                  have assump_2153 : True := by
                                    apply True.intro
                                  let assump_553 := assump_15 assump_2153
                                  apply False.elim assump_553
                            case inr assump_527 =>
                              cases assump_494
                              case inl assump_559 =>
                                cases assump_559
                                case intro assump_561 assump_562 =>
                                  have assump_2154 : True := by
                                    apply True.intro
                                  let assump_569 := assump_15 assump_2154
                                  apply False.elim assump_569
                              case inr assump_560 =>
                                cases assump_560
                                case intro assump_573 assump_574 =>
                                  have assump_2155 : True := by
                                    apply True.intro
                                  let assump_582 := assump_15 assump_2155
                                  apply False.elim assump_582
                      case inr assump_492 =>
                        have assump_2156 : True := by
                          apply True.intro
                        let assump_593 := assump_15 assump_2156
                        apply False.elim assump_593
                    case inr assump_488 =>
                      apply False.elim assump_488
                  case inr assump_486 =>
                    cases assump_3
                    case inl assump_601 =>
                      cases assump_601
                      case intro assump_603 assump_604 =>
                        cases assump_603
                        case inl assump_605 =>
                          cases assump_604
                          case inl assump_609 =>
                            cases assump_609
                            case intro assump_611 assump_612 =>
                              have assump_2157 : True := by
                                apply True.intro
                              let assump_620 := assump_15 assump_2157
                              apply False.elim assump_620
                          case inr assump_610 =>
                            cases assump_610
                            case intro assump_624 assump_625 =>
                              have assump_2158 : True := by
                                apply True.intro
                              let assump_634 := assump_15 assump_2158
                              apply False.elim assump_634
                        case inr assump_606 =>
                          cases assump_606
                          case inl assump_638 =>
                            cases assump_604
                            case inl assump_642 =>
                              cases assump_642
                              case intro assump_644 assump_645 =>
                                have assump_2159 : True := by
                                  apply True.intro
                                let assump_653 := assump_15 assump_2159
                                apply False.elim assump_653
                            case inr assump_643 =>
                              cases assump_643
                              case intro assump_657 assump_658 =>
                                have assump_2160 : True := by
                                  apply True.intro
                                let assump_667 := assump_15 assump_2160
                                apply False.elim assump_667
                          case inr assump_639 =>
                            cases assump_604
                            case inl assump_673 =>
                              cases assump_673
                              case intro assump_675 assump_676 =>
                                have assump_2161 : True := by
                                  apply True.intro
                                let assump_684 := assump_15 assump_2161
                                apply False.elim assump_684
                            case inr assump_674 =>
                              cases assump_674
                              case intro assump_688 assump_689 =>
                                have assump_2162 : True := by
                                  apply True.intro
                                let assump_698 := assump_15 assump_2162
                                apply False.elim assump_698
                    case inr assump_602 =>
                      have assump_2163 : True := by
                        apply True.intro
                      let assump_710 := assump_15 assump_2163
                      apply False.elim assump_710
          case inr assump_11 =>
            cases assump_7
            case intro assump_716 assump_717 =>
              cases assump_716
              case inl assump_718 =>
                cases assump_5
                case inl assump_724 =>
                  cases assump_3
                  case inl assump_728 =>
                    cases assump_728
                    case intro assump_730 assump_731 =>
                      cases assump_730
                      case inl assump_732 =>
                        cases assump_731
                        case inl assump_736 =>
                          cases assump_736
                          case intro assump_738 assump_739 =>
                            have assump_2164 : True := by
                              apply True.intro
                            let assump_747 := assump_717 assump_2164
                            apply False.elim assump_747
                        case inr assump_737 =>
                          cases assump_737
                          case intro assump_751 assump_752 =>
                            have assump_2165 : True := by
                              apply True.intro
                            let assump_761 := assump_717 assump_2165
                            apply False.elim assump_761
                      case inr assump_733 =>
                        cases assump_733
                        case inl assump_765 =>
                          cases assump_731
                          case inl assump_769 =>
                            cases assump_769
                            case intro assump_771 assump_772 =>
                              have assump_2166 : (False ∨ p2) := by
                                apply Or.inr
                                exact assump_765
                              let assump_779 := assump_724 assump_2166
                              apply False.elim assump_779
                          case inr assump_770 =>
                            cases assump_770
                            case intro assump_783 assump_784 =>
                              have assump_2167 : (False ∨ p2) := by
                                apply Or.inr
                                exact assump_765
                              let assump_792 := assump_724 assump_2167
                              apply False.elim assump_792
                        case inr assump_766 =>
                          cases assump_731
                          case inl assump_798 =>
                            cases assump_798
                            case intro assump_800 assump_801 =>
                              have assump_2168 : True := by
                                apply True.intro
                              let assump_809 := assump_717 assump_2168
                              apply False.elim assump_809
                          case inr assump_799 =>
                            cases assump_799
                            case intro assump_813 assump_814 =>
                              have assump_2169 : True := by
                                apply True.intro
                              let assump_823 := assump_717 assump_2169
                              apply False.elim assump_823
                  case inr assump_729 =>
                    have assump_2170 : True := by
                      apply True.intro
                    let assump_835 := assump_717 assump_2170
                    apply False.elim assump_835
                case inr assump_725 =>
                  cases assump_725
                  case inl assump_839 =>
                    cases assump_839
                    case inl assump_841 =>
                      cases assump_3
                      case inl assump_845 =>
                        cases assump_845
                        case intro assump_847 assump_848 =>
                          cases assump_847
                          case inl assump_849 =>
                            cases assump_848
                            case inl assump_853 =>
                              cases assump_853
                              case intro assump_855 assump_856 =>
                                have assump_2171 : True := by
                                  apply True.intro
                                let assump_863 := assump_717 assump_2171
                                apply False.elim assump_863
                            case inr assump_854 =>
                              cases assump_854
                              case intro assump_867 assump_868 =>
                                have assump_2172 : True := by
                                  apply True.intro
                                let assump_876 := assump_717 assump_2172
                                apply False.elim assump_876
                          case inr assump_850 =>
                            cases assump_850
                            case inl assump_880 =>
                              cases assump_848
                              case inl assump_884 =>
                                cases assump_884
                                case intro assump_886 assump_887 =>
                                  have assump_2173 : True := by
                                    apply True.intro
                                  let assump_894 := assump_717 assump_2173
                                  apply False.elim assump_894
                              case inr assump_885 =>
                                cases assump_885
                                case intro assump_898 assump_899 =>
                                  have assump_2174 : True := by
                                    apply True.intro
                                  let assump_907 := assump_717 assump_2174
                                  apply False.elim assump_907
                            case inr assump_881 =>
                              cases assump_848
                              case inl assump_913 =>
                                cases assump_913
                                case intro assump_915 assump_916 =>
                                  have assump_2175 : True := by
                                    apply True.intro
                                  let assump_923 := assump_717 assump_2175
                                  apply False.elim assump_923
                              case inr assump_914 =>
                                cases assump_914
                                case intro assump_927 assump_928 =>
                                  have assump_2176 : True := by
                                    apply True.intro
                                  let assump_936 := assump_717 assump_2176
                                  apply False.elim assump_936
                      case inr assump_846 =>
                        have assump_2177 : True := by
                          apply True.intro
                        let assump_947 := assump_717 assump_2177
                        apply False.elim assump_947
                    case inr assump_842 =>
                      apply False.elim assump_842
                  case inr assump_840 =>
                    cases assump_3
                    case inl assump_955 =>
                      cases assump_955
                      case intro assump_957 assump_958 =>
                        cases assump_957
                        case inl assump_959 =>
                          cases assump_958
                          case inl assump_963 =>
                            cases assump_963
                            case intro assump_965 assump_966 =>
                              have assump_2178 : True := by
                                apply True.intro
                              let assump_974 := assump_717 assump_2178
                              apply False.elim assump_974
                          case inr assump_964 =>
                            cases assump_964
                            case intro assump_978 assump_979 =>
                              have assump_2179 : True := by
                                apply True.intro
                              let assump_988 := assump_717 assump_2179
                              apply False.elim assump_988
                        case inr assump_960 =>
                          cases assump_960
                          case inl assump_992 =>
                            cases assump_958
                            case inl assump_996 =>
                              cases assump_996
                              case intro assump_998 assump_999 =>
                                have assump_2180 : True := by
                                  apply True.intro
                                let assump_1007 := assump_717 assump_2180
                                apply False.elim assump_1007
                            case inr assump_997 =>
                              cases assump_997
                              case intro assump_1011 assump_1012 =>
                                have assump_2181 : True := by
                                  apply True.intro
                                let assump_1021 := assump_717 assump_2181
                                apply False.elim assump_1021
                          case inr assump_993 =>
                            cases assump_958
                            case inl assump_1027 =>
                              cases assump_1027
                              case intro assump_1029 assump_1030 =>
                                have assump_2182 : True := by
                                  apply True.intro
                                let assump_1038 := assump_717 assump_2182
                                apply False.elim assump_1038
                            case inr assump_1028 =>
                              cases assump_1028
                              case intro assump_1042 assump_1043 =>
                                have assump_2183 : True := by
                                  apply True.intro
                                let assump_1052 := assump_717 assump_2183
                                apply False.elim assump_1052
                    case inr assump_956 =>
                      have assump_2184 : True := by
                        apply True.intro
                      let assump_1064 := assump_717 assump_2184
                      apply False.elim assump_1064
              case inr assump_719 =>
                cases assump_5
                case inl assump_1072 =>
                  cases assump_3
                  case inl assump_1076 =>
                    cases assump_1076
                    case intro assump_1078 assump_1079 =>
                      cases assump_1078
                      case inl assump_1080 =>
                        cases assump_1079
                        case inl assump_1084 =>
                          cases assump_1084
                          case intro assump_1086 assump_1087 =>
                            have assump_2185 : True := by
                              apply True.intro
                            let assump_1095 := assump_717 assump_2185
                            apply False.elim assump_1095
                        case inr assump_1085 =>
                          cases assump_1085
                          case intro assump_1099 assump_1100 =>
                            have assump_2186 : True := by
                              apply True.intro
                            let assump_1109 := assump_717 assump_2186
                            apply False.elim assump_1109
                      case inr assump_1081 =>
                        cases assump_1081
                        case inl assump_1113 =>
                          cases assump_1079
                          case inl assump_1117 =>
                            cases assump_1117
                            case intro assump_1119 assump_1120 =>
                              have assump_2187 : (False ∨ p2) := by
                                apply Or.inr
                                exact assump_1113
                              let assump_1127 := assump_1072 assump_2187
                              apply False.elim assump_1127
                          case inr assump_1118 =>
                            cases assump_1118
                            case intro assump_1131 assump_1132 =>
                              have assump_2188 : (False ∨ p2) := by
                                apply Or.inr
                                exact assump_1113
                              let assump_1140 := assump_1072 assump_2188
                              apply False.elim assump_1140
                        case inr assump_1114 =>
                          cases assump_1079
                          case inl assump_1146 =>
                            cases assump_1146
                            case intro assump_1148 assump_1149 =>
                              have assump_2189 : True := by
                                apply True.intro
                              let assump_1157 := assump_717 assump_2189
                              apply False.elim assump_1157
                          case inr assump_1147 =>
                            cases assump_1147
                            case intro assump_1161 assump_1162 =>
                              have assump_2190 : True := by
                                apply True.intro
                              let assump_1171 := assump_717 assump_2190
                              apply False.elim assump_1171
                  case inr assump_1077 =>
                    have assump_2191 : True := by
                      apply True.intro
                    let assump_1183 := assump_717 assump_2191
                    apply False.elim assump_1183
                case inr assump_1073 =>
                  cases assump_1073
                  case inl assump_1187 =>
                    cases assump_1187
                    case inl assump_1189 =>
                      cases assump_3
                      case inl assump_1193 =>
                        cases assump_1193
                        case intro assump_1195 assump_1196 =>
                          cases assump_1195
                          case inl assump_1197 =>
                            cases assump_1196
                            case inl assump_1201 =>
                              cases assump_1201
                              case intro assump_1203 assump_1204 =>
                                have assump_2192 : True := by
                                  apply True.intro
                                let assump_1211 := assump_717 assump_2192
                                apply False.elim assump_1211
                            case inr assump_1202 =>
                              cases assump_1202
                              case intro assump_1215 assump_1216 =>
                                have assump_2193 : True := by
                                  apply True.intro
                                let assump_1224 := assump_717 assump_2193
                                apply False.elim assump_1224
                          case inr assump_1198 =>
                            cases assump_1198
                            case inl assump_1228 =>
                              cases assump_1196
                              case inl assump_1232 =>
                                cases assump_1232
                                case intro assump_1234 assump_1235 =>
                                  have assump_2194 : True := by
                                    apply True.intro
                                  let assump_1242 := assump_717 assump_2194
                                  apply False.elim assump_1242
                              case inr assump_1233 =>
                                cases assump_1233
                                case intro assump_1246 assump_1247 =>
                                  have assump_2195 : True := by
                                    apply True.intro
                                  let assump_1255 := assump_717 assump_2195
                                  apply False.elim assump_1255
                            case inr assump_1229 =>
                              cases assump_1196
                              case inl assump_1261 =>
                                cases assump_1261
                                case intro assump_1263 assump_1264 =>
                                  have assump_2196 : True := by
                                    apply True.intro
                                  let assump_1271 := assump_717 assump_2196
                                  apply False.elim assump_1271
                              case inr assump_1262 =>
                                cases assump_1262
                                case intro assump_1275 assump_1276 =>
                                  have assump_2197 : True := by
                                    apply True.intro
                                  let assump_1284 := assump_717 assump_2197
                                  apply False.elim assump_1284
                      case inr assump_1194 =>
                        have assump_2198 : True := by
                          apply True.intro
                        let assump_1295 := assump_717 assump_2198
                        apply False.elim assump_1295
                    case inr assump_1190 =>
                      apply False.elim assump_1190
                  case inr assump_1188 =>
                    cases assump_3
                    case inl assump_1303 =>
                      cases assump_1303
                      case intro assump_1305 assump_1306 =>
                        cases assump_1305
                        case inl assump_1307 =>
                          cases assump_1306
                          case inl assump_1311 =>
                            cases assump_1311
                            case intro assump_1313 assump_1314 =>
                              have assump_2199 : True := by
                                apply True.intro
                              let assump_1322 := assump_717 assump_2199
                              apply False.elim assump_1322
                          case inr assump_1312 =>
                            cases assump_1312
                            case intro assump_1326 assump_1327 =>
                              have assump_2200 : True := by
                                apply True.intro
                              let assump_1336 := assump_717 assump_2200
                              apply False.elim assump_1336
                        case inr assump_1308 =>
                          cases assump_1308
                          case inl assump_1340 =>
                            cases assump_1306
                            case inl assump_1344 =>
                              cases assump_1344
                              case intro assump_1346 assump_1347 =>
                                have assump_2201 : True := by
                                  apply True.intro
                                let assump_1355 := assump_717 assump_2201
                                apply False.elim assump_1355
                            case inr assump_1345 =>
                              cases assump_1345
                              case intro assump_1359 assump_1360 =>
                                have assump_2202 : True := by
                                  apply True.intro
                                let assump_1369 := assump_717 assump_2202
                                apply False.elim assump_1369
                          case inr assump_1341 =>
                            cases assump_1306
                            case inl assump_1375 =>
                              cases assump_1375
                              case intro assump_1377 assump_1378 =>
                                have assump_2203 : True := by
                                  apply True.intro
                                let assump_1386 := assump_717 assump_2203
                                apply False.elim assump_1386
                            case inr assump_1376 =>
                              cases assump_1376
                              case intro assump_1390 assump_1391 =>
                                have assump_2204 : True := by
                                  apply True.intro
                                let assump_1400 := assump_717 assump_2204
                                apply False.elim assump_1400
                    case inr assump_1304 =>
                      have assump_2205 : True := by
                        apply True.intro
                      let assump_1412 := assump_717 assump_2205
                      apply False.elim assump_1412
        case inr assump_9 =>
          cases assump_9
          case inl assump_1416 =>
            cases assump_7
            case intro assump_1420 assump_1421 =>
              cases assump_1420
              case inl assump_1422 =>
                cases assump_5
                case inl assump_1428 =>
                  cases assump_3
                  case inl assump_1432 =>
                    cases assump_1432
                    case intro assump_1434 assump_1435 =>
                      cases assump_1434
                      case inl assump_1436 =>
                        cases assump_1435
                        case inl assump_1440 =>
                          cases assump_1440
                          case intro assump_1442 assump_1443 =>
                            have assump_2206 : True := by
                              apply True.intro
                            let assump_1451 := assump_1421 assump_2206
                            apply False.elim assump_1451
                        case inr assump_1441 =>
                          cases assump_1441
                          case intro assump_1455 assump_1456 =>
                            have assump_2207 : True := by
                              apply True.intro
                            let assump_1465 := assump_1421 assump_2207
                            apply False.elim assump_1465
                      case inr assump_1437 =>
                        cases assump_1437
                        case inl assump_1469 =>
                          cases assump_1435
                          case inl assump_1473 =>
                            cases assump_1473
                            case intro assump_1475 assump_1476 =>
                              have assump_2208 : (False ∨ p2) := by
                                apply Or.inr
                                exact assump_1469
                              let assump_1483 := assump_1428 assump_2208
                              apply False.elim assump_1483
                          case inr assump_1474 =>
                            cases assump_1474
                            case intro assump_1487 assump_1488 =>
                              have assump_2209 : (False ∨ p2) := by
                                apply Or.inr
                                exact assump_1469
                              let assump_1496 := assump_1428 assump_2209
                              apply False.elim assump_1496
                        case inr assump_1470 =>
                          cases assump_1435
                          case inl assump_1502 =>
                            cases assump_1502
                            case intro assump_1504 assump_1505 =>
                              have assump_2210 : True := by
                                apply True.intro
                              let assump_1513 := assump_1421 assump_2210
                              apply False.elim assump_1513
                          case inr assump_1503 =>
                            cases assump_1503
                            case intro assump_1517 assump_1518 =>
                              have assump_2211 : True := by
                                apply True.intro
                              let assump_1527 := assump_1421 assump_2211
                              apply False.elim assump_1527
                  case inr assump_1433 =>
                    have assump_2212 : True := by
                      apply True.intro
                    let assump_1539 := assump_1421 assump_2212
                    apply False.elim assump_1539
                case inr assump_1429 =>
                  cases assump_1429
                  case inl assump_1543 =>
                    cases assump_1543
                    case inl assump_1545 =>
                      cases assump_3
                      case inl assump_1549 =>
                        cases assump_1549
                        case intro assump_1551 assump_1552 =>
                          cases assump_1551
                          case inl assump_1553 =>
                            cases assump_1552
                            case inl assump_1557 =>
                              cases assump_1557
                              case intro assump_1559 assump_1560 =>
                                have assump_2213 : True := by
                                  apply True.intro
                                let assump_1567 := assump_1421 assump_2213
                                apply False.elim assump_1567
                            case inr assump_1558 =>
                              cases assump_1558
                              case intro assump_1571 assump_1572 =>
                                have assump_2214 : True := by
                                  apply True.intro
                                let assump_1580 := assump_1421 assump_2214
                                apply False.elim assump_1580
                          case inr assump_1554 =>
                            cases assump_1554
                            case inl assump_1584 =>
                              cases assump_1552
                              case inl assump_1588 =>
                                cases assump_1588
                                case intro assump_1590 assump_1591 =>
                                  have assump_2215 : True := by
                                    apply True.intro
                                  let assump_1598 := assump_1421 assump_2215
                                  apply False.elim assump_1598
                              case inr assump_1589 =>
                                cases assump_1589
                                case intro assump_1602 assump_1603 =>
                                  have assump_2216 : True := by
                                    apply True.intro
                                  let assump_1611 := assump_1421 assump_2216
                                  apply False.elim assump_1611
                            case inr assump_1585 =>
                              cases assump_1552
                              case inl assump_1617 =>
                                cases assump_1617
                                case intro assump_1619 assump_1620 =>
                                  have assump_2217 : True := by
                                    apply True.intro
                                  let assump_1627 := assump_1421 assump_2217
                                  apply False.elim assump_1627
                              case inr assump_1618 =>
                                cases assump_1618
                                case intro assump_1631 assump_1632 =>
                                  have assump_2218 : True := by
                                    apply True.intro
                                  let assump_1640 := assump_1421 assump_2218
                                  apply False.elim assump_1640
                      case inr assump_1550 =>
                        have assump_2219 : True := by
                          apply True.intro
                        let assump_1651 := assump_1421 assump_2219
                        apply False.elim assump_1651
                    case inr assump_1546 =>
                      apply False.elim assump_1546
                  case inr assump_1544 =>
                    cases assump_3
                    case inl assump_1659 =>
                      cases assump_1659
                      case intro assump_1661 assump_1662 =>
                        cases assump_1661
                        case inl assump_1663 =>
                          cases assump_1662
                          case inl assump_1667 =>
                            cases assump_1667
                            case intro assump_1669 assump_1670 =>
                              have assump_2220 : True := by
                                apply True.intro
                              let assump_1678 := assump_1421 assump_2220
                              apply False.elim assump_1678
                          case inr assump_1668 =>
                            cases assump_1668
                            case intro assump_1682 assump_1683 =>
                              have assump_2221 : True := by
                                apply True.intro
                              let assump_1692 := assump_1421 assump_2221
                              apply False.elim assump_1692
                        case inr assump_1664 =>
                          cases assump_1664
                          case inl assump_1696 =>
                            cases assump_1662
                            case inl assump_1700 =>
                              cases assump_1700
                              case intro assump_1702 assump_1703 =>
                                have assump_2222 : True := by
                                  apply True.intro
                                let assump_1711 := assump_1421 assump_2222
                                apply False.elim assump_1711
                            case inr assump_1701 =>
                              cases assump_1701
                              case intro assump_1715 assump_1716 =>
                                have assump_2223 : True := by
                                  apply True.intro
                                let assump_1725 := assump_1421 assump_2223
                                apply False.elim assump_1725
                          case inr assump_1697 =>
                            cases assump_1662
                            case inl assump_1731 =>
                              cases assump_1731
                              case intro assump_1733 assump_1734 =>
                                have assump_2224 : True := by
                                  apply True.intro
                                let assump_1742 := assump_1421 assump_2224
                                apply False.elim assump_1742
                            case inr assump_1732 =>
                              cases assump_1732
                              case intro assump_1746 assump_1747 =>
                                have assump_2225 : True := by
                                  apply True.intro
                                let assump_1756 := assump_1421 assump_2225
                                apply False.elim assump_1756
                    case inr assump_1660 =>
                      have assump_2226 : True := by
                        apply True.intro
                      let assump_1768 := assump_1421 assump_2226
                      apply False.elim assump_1768
              case inr assump_1423 =>
                cases assump_5
                case inl assump_1776 =>
                  cases assump_3
                  case inl assump_1780 =>
                    cases assump_1780
                    case intro assump_1782 assump_1783 =>
                      cases assump_1782
                      case inl assump_1784 =>
                        cases assump_1783
                        case inl assump_1788 =>
                          cases assump_1788
                          case intro assump_1790 assump_1791 =>
                            have assump_2227 : True := by
                              apply True.intro
                            let assump_1799 := assump_1421 assump_2227
                            apply False.elim assump_1799
                        case inr assump_1789 =>
                          cases assump_1789
                          case intro assump_1803 assump_1804 =>
                            have assump_2228 : True := by
                              apply True.intro
                            let assump_1813 := assump_1421 assump_2228
                            apply False.elim assump_1813
                      case inr assump_1785 =>
                        cases assump_1785
                        case inl assump_1817 =>
                          cases assump_1783
                          case inl assump_1821 =>
                            cases assump_1821
                            case intro assump_1823 assump_1824 =>
                              have assump_2229 : (False ∨ p2) := by
                                apply Or.inr
                                exact assump_1817
                              let assump_1831 := assump_1776 assump_2229
                              apply False.elim assump_1831
                          case inr assump_1822 =>
                            cases assump_1822
                            case intro assump_1835 assump_1836 =>
                              have assump_2230 : (False ∨ p2) := by
                                apply Or.inr
                                exact assump_1817
                              let assump_1844 := assump_1776 assump_2230
                              apply False.elim assump_1844
                        case inr assump_1818 =>
                          cases assump_1783
                          case inl assump_1850 =>
                            cases assump_1850
                            case intro assump_1852 assump_1853 =>
                              have assump_2231 : True := by
                                apply True.intro
                              let assump_1861 := assump_1421 assump_2231
                              apply False.elim assump_1861
                          case inr assump_1851 =>
                            cases assump_1851
                            case intro assump_1865 assump_1866 =>
                              have assump_2232 : True := by
                                apply True.intro
                              let assump_1875 := assump_1421 assump_2232
                              apply False.elim assump_1875
                  case inr assump_1781 =>
                    have assump_2233 : True := by
                      apply True.intro
                    let assump_1887 := assump_1421 assump_2233
                    apply False.elim assump_1887
                case inr assump_1777 =>
                  cases assump_1777
                  case inl assump_1891 =>
                    cases assump_1891
                    case inl assump_1893 =>
                      cases assump_3
                      case inl assump_1897 =>
                        cases assump_1897
                        case intro assump_1899 assump_1900 =>
                          cases assump_1899
                          case inl assump_1901 =>
                            cases assump_1900
                            case inl assump_1905 =>
                              cases assump_1905
                              case intro assump_1907 assump_1908 =>
                                have assump_2234 : True := by
                                  apply True.intro
                                let assump_1915 := assump_1421 assump_2234
                                apply False.elim assump_1915
                            case inr assump_1906 =>
                              cases assump_1906
                              case intro assump_1919 assump_1920 =>
                                have assump_2235 : True := by
                                  apply True.intro
                                let assump_1928 := assump_1421 assump_2235
                                apply False.elim assump_1928
                          case inr assump_1902 =>
                            cases assump_1902
                            case inl assump_1932 =>
                              cases assump_1900
                              case inl assump_1936 =>
                                cases assump_1936
                                case intro assump_1938 assump_1939 =>
                                  have assump_2236 : True := by
                                    apply True.intro
                                  let assump_1946 := assump_1421 assump_2236
                                  apply False.elim assump_1946
                              case inr assump_1937 =>
                                cases assump_1937
                                case intro assump_1950 assump_1951 =>
                                  have assump_2237 : True := by
                                    apply True.intro
                                  let assump_1959 := assump_1421 assump_2237
                                  apply False.elim assump_1959
                            case inr assump_1933 =>
                              cases assump_1900
                              case inl assump_1965 =>
                                cases assump_1965
                                case intro assump_1967 assump_1968 =>
                                  have assump_2238 : True := by
                                    apply True.intro
                                  let assump_1975 := assump_1421 assump_2238
                                  apply False.elim assump_1975
                              case inr assump_1966 =>
                                cases assump_1966
                                case intro assump_1979 assump_1980 =>
                                  have assump_2239 : True := by
                                    apply True.intro
                                  let assump_1988 := assump_1421 assump_2239
                                  apply False.elim assump_1988
                      case inr assump_1898 =>
                        have assump_2240 : True := by
                          apply True.intro
                        let assump_1999 := assump_1421 assump_2240
                        apply False.elim assump_1999
                    case inr assump_1894 =>
                      apply False.elim assump_1894
                  case inr assump_1892 =>
                    cases assump_3
                    case inl assump_2007 =>
                      cases assump_2007
                      case intro assump_2009 assump_2010 =>
                        cases assump_2009
                        case inl assump_2011 =>
                          cases assump_2010
                          case inl assump_2015 =>
                            cases assump_2015
                            case intro assump_2017 assump_2018 =>
                              have assump_2241 : True := by
                                apply True.intro
                              let assump_2026 := assump_1421 assump_2241
                              apply False.elim assump_2026
                          case inr assump_2016 =>
                            cases assump_2016
                            case intro assump_2030 assump_2031 =>
                              have assump_2242 : True := by
                                apply True.intro
                              let assump_2040 := assump_1421 assump_2242
                              apply False.elim assump_2040
                        case inr assump_2012 =>
                          cases assump_2012
                          case inl assump_2044 =>
                            cases assump_2010
                            case inl assump_2048 =>
                              cases assump_2048
                              case intro assump_2050 assump_2051 =>
                                have assump_2243 : True := by
                                  apply True.intro
                                let assump_2059 := assump_1421 assump_2243
                                apply False.elim assump_2059
                            case inr assump_2049 =>
                              cases assump_2049
                              case intro assump_2063 assump_2064 =>
                                have assump_2244 : True := by
                                  apply True.intro
                                let assump_2073 := assump_1421 assump_2244
                                apply False.elim assump_2073
                          case inr assump_2045 =>
                            cases assump_2010
                            case inl assump_2079 =>
                              cases assump_2079
                              case intro assump_2081 assump_2082 =>
                                have assump_2245 : True := by
                                  apply True.intro
                                let assump_2090 := assump_1421 assump_2245
                                apply False.elim assump_2090
                            case inr assump_2080 =>
                              cases assump_2080
                              case intro assump_2094 assump_2095 =>
                                have assump_2246 : True := by
                                  apply True.intro
                                let assump_2104 := assump_1421 assump_2246
                                apply False.elim assump_2104
                    case inr assump_2008 =>
                      have assump_2247 : True := by
                        apply True.intro
                      let assump_2116 := assump_1421 assump_2247
                      apply False.elim assump_2116
          case inr assump_1417 =>
            apply False.elim assump_1417


variable (p2 p5 p7 p6 p0 : Prop)
theorem file73_201379 : (((((p2 → p7) ∧ (p5 ∧ p0)) → ((p0 ∨ False) ∨ (p6 → p5))) → False) → False) := by
  intro assump_1
  have assump_19 : (((p2 → p7) ∧ (p5 ∧ p0)) → ((p0 ∨ False) ∨ (p6 → p5))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply Or.inl
        exact assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p7 p1 p3 p6 p0 : Prop)
theorem file73_201880 : (((((True ∧ p7) → False) → ((p1 ∧ False) → False)) ∨ (((p3 → p3) → False) ∧ ((p6 ∨ True) ∧ (False → p6)))) ∨ ((((p7 → False) → False) → False) → (((p0 ∧ p1) ∨ (p1 ∧ p0)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_4


variable (p2 p3 p1 p6 p5 : Prop)
theorem file73_202269 : ((((((p5 → p1) → (p2 ∨ True)) ∨ ((p5 → False) → False)) → False) ∧ ((((p1 ∨ p6) → False) → ((p3 ∧ p6) → (p2 ∧ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_38 : (((p1 ∨ p6) → False) → ((p3 ∧ p6) → (p2 ∧ p1))) := by
      intro assump_9
      intro assump_10
      apply And.intro
      cases assump_10
      case intro assump_11 assump_12 =>
        have assump_39 : (p1 ∨ p6) := by
          apply Or.inr
          exact assump_12
        let assump_19 := assump_9 assump_39
        apply False.elim assump_19
      cases assump_10
      case intro assump_23 assump_24 =>
        have assump_40 : (p1 ∨ p6) := by
          apply Or.inr
          exact assump_24
        let assump_31 := assump_9 assump_40
        apply False.elim assump_31
    let assump_8 := assump_3 assump_38
    apply False.elim assump_8


variable (p0 p4 p6 p3 p5 p1 : Prop)
theorem file73_203209 : ((((((p3 ∨ p4) → (p6 → p5)) ∧ ((False ∨ p1) ∧ (p6 ∧ p4))) ∧ (((p3 ∧ p3) ∨ (False ∨ True)) → ((False → p4) → False))) ∨ ((((True ∨ True) ∨ (p3 → p0)) → False) ∧ (((False → False) ∨ (p3 → False)) → False))) → False) := by
  intro assump_12
  cases assump_12
  case inl assump_13 =>
    cases assump_13
    case intro assump_15 assump_16 =>
      cases assump_15
      case intro assump_17 assump_18 =>
        cases assump_18
        case intro assump_21 assump_22 =>
          cases assump_21
          case inl assump_23 =>
            apply False.elim assump_23
          case inr assump_24 =>
            cases assump_22
            case intro assump_29 assump_30 =>
              have assump_58 : ((p3 ∧ p3) ∨ (False ∨ True)) := by
                apply Or.inr
                apply Or.inr
                apply True.intro
              let assump_37 := assump_16 assump_58
              have assump_59 : (False → p4) := by
                intro assump_39
                apply False.elim assump_39
              let assump_38 := assump_37 assump_59
              apply False.elim assump_38
  case inr assump_14 =>
    cases assump_14
    case intro assump_45 assump_46 =>
      have assump_60 : ((False → False) ∨ (p3 → False)) := by
        apply Or.inl
        intro assump_52
        apply False.elim assump_52
      let assump_51 := assump_46 assump_60
      apply False.elim assump_51


variable (p4 p0 p6 p5 p7 p2 p1 : Prop)
theorem file73_204666 : (((((p6 ∧ p4) ∧ (p4 ∨ p4)) ∧ ((p7 → False) → (p7 → False))) ∨ (((True ∧ True) ∨ (p1 → False)) ∧ ((p5 ∧ False) → False))) ∧ ((((p4 → False) → (p4 → False)) → False) → (((p2 → p0) → False) → ((p1 ∧ True) ∨ (p5 ∧ p4))))) := by
  apply And.intro
  apply Or.inr
  apply And.intro
  apply Or.inl
  apply And.intro
  apply True.intro
  apply True.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3
  intro assump_8
  intro assump_9
  have assump_28 : ((p4 → False) → (p4 → False)) := by
    intro assump_15
    intro assump_16
    have assump_29 : p4 := by
      exact assump_16
    let assump_21 := assump_15 assump_29
    apply False.elim assump_21
  let assump_14 := assump_8 assump_28
  apply False.elim assump_14


variable (p7 p5 p3 p0 p6 p1 p4 : Prop)
theorem file73_205493 : ((((((p5 ∧ p4) ∨ (p0 → p7)) → False) → (((p3 → False) → False) ∨ ((False ∧ p0) ∨ (p4 ∨ p7)))) ∧ ((((p6 ∧ p3) ∨ (p1 ∧ True)) → ((True ∧ p1) → (p0 → p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_37 : (((p6 ∧ p3) ∨ (p1 ∧ True)) → ((True ∧ p1) → (p0 → p1))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      cases assump_10
      case intro assump_14 assump_15 =>
        cases assump_9
        case inl assump_20 =>
          cases assump_20
          case intro assump_22 assump_23 =>
            exact assump_15
        case inr assump_21 =>
          cases assump_21
          case intro assump_28 assump_29 =>
            exact assump_28
    let assump_8 := assump_3 assump_37
    apply False.elim assump_8


variable (p2 p4 p6 p0 p7 p1 : Prop)
theorem file73_206357 : ((((((p6 ∧ p6) ∧ (p2 → False)) ∧ ((p0 → p7) ∧ (True → False))) ∨ (((p1 ∧ p2) ∧ (p4 ∨ False)) ∨ ((p2 ∧ p7) ∨ (p1 → True)))) → False) → False) := by
  intro assump_1
  have assump_9 : ((((p6 ∧ p6) ∧ (p2 → False)) ∧ ((p0 → p7) ∧ (True → False))) ∨ (((p1 ∧ p2) ∧ (p4 ∨ False)) ∨ ((p2 ∧ p7) ∨ (p1 → True)))) := by
    apply Or.inr
    apply Or.inr
    apply Or.inr
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p5 p6 p2 p7 p4 p1 p0 : Prop)
theorem file73_206884 : (((((p7 → p0) ∨ (False ∨ False)) → ((p4 ∧ p4) ∨ (p4 → False))) → False) → ((((p0 ∨ p1) → False) ∧ ((p0 ∧ p6) → False)) ∨ (((p5 → False) → (p2 ∨ p5)) ∨ ((p6 → False) ∧ (p6 → False))))) := by
  intro assump_5
  apply Or.inl
  apply And.intro
  intro assump_8
  cases assump_8
  case inl assump_9 =>
    have assump_135 : (((p7 → p0) ∨ (False ∨ False)) → ((p4 ∧ p4) ∨ (p4 → False))) := by
      intro assump_15
      cases assump_15
      case inl assump_16 =>
        apply Or.inr
        intro assump_20
        have assump_136 : (((p7 → p0) ∨ (False ∨ False)) → ((p4 ∧ p4) ∨ (p4 → False))) := by
          intro assump_27
          cases assump_27
          case inl assump_28 =>
            apply Or.inl
            apply And.intro
            exact assump_20
            exact assump_20
          case inr assump_29 =>
            cases assump_29
            case inl assump_32 =>
              apply False.elim assump_32
            case inr assump_33 =>
              apply False.elim assump_33
        let assump_26 := assump_5 assump_136
        apply False.elim assump_26
      case inr assump_17 =>
        cases assump_17
        case inl assump_41 =>
          apply False.elim assump_41
        case inr assump_42 =>
          apply False.elim assump_42
    let assump_14 := assump_5 assump_135
    apply False.elim assump_14
  case inr assump_10 =>
    have assump_137 : (((p7 → p0) ∨ (False ∨ False)) → ((p4 ∧ p4) ∨ (p4 → False))) := by
      intro assump_54
      cases assump_54
      case inl assump_55 =>
        apply Or.inr
        intro assump_59
        have assump_138 : (((p7 → p0) ∨ (False ∨ False)) → ((p4 ∧ p4) ∨ (p4 → False))) := by
          intro assump_66
          cases assump_66
          case inl assump_67 =>
            apply Or.inl
            apply And.intro
            exact assump_59
            exact assump_59
          case inr assump_68 =>
            cases assump_68
            case inl assump_71 =>
              apply False.elim assump_71
            case inr assump_72 =>
              apply False.elim assump_72
        let assump_65 := assump_5 assump_138
        apply False.elim assump_65
      case inr assump_56 =>
        cases assump_56
        case inl assump_80 =>
          apply False.elim assump_80
        case inr assump_81 =>
          apply False.elim assump_81
    let assump_53 := assump_5 assump_137
    apply False.elim assump_53
  intro assump_89
  cases assump_89
  case intro assump_90 assump_91 =>
    have assump_139 : (((p7 → p0) ∨ (False ∨ False)) → ((p4 ∧ p4) ∨ (p4 → False))) := by
      intro assump_99
      cases assump_99
      case inl assump_100 =>
        apply Or.inr
        intro assump_104
        have assump_140 : (((p7 → p0) ∨ (False ∨ False)) → ((p4 ∧ p4) ∨ (p4 → False))) := by
          intro assump_112
          cases assump_112
          case inl assump_113 =>
            apply Or.inl
            apply And.intro
            exact assump_104
            exact assump_104
          case inr assump_114 =>
            cases assump_114
            case inl assump_117 =>
              apply False.elim assump_117
            case inr assump_118 =>
              apply False.elim assump_118
        let assump_111 := assump_5 assump_140
        apply False.elim assump_111
      case inr assump_101 =>
        cases assump_101
        case inl assump_126 =>
          apply False.elim assump_126
        case inr assump_127 =>
          apply False.elim assump_127
    let assump_98 := assump_5 assump_139
    apply False.elim assump_98


variable (p7 p2 p5 p0 p3 p6 : Prop)
theorem file73_210478 : (((((p2 ∨ p2) ∧ (False → False)) → ((True → p5) → False)) → (((p3 → p7) ∧ (p5 ∨ p5)) → ((p6 ∨ p2) → False))) → ((((True → False) → False) → False) → (((True → False) → (True → p0)) ∨ ((False → False) ∧ (p3 → False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  intro assump_8
  have assump_17 : True := by
    apply True.intro
  let assump_13 := assump_7 assump_17
  apply False.elim assump_13


variable (p0 p7 p5 p2 p3 p1 p4 : Prop)
theorem file73_210967 : (((((True ∨ p7) → False) ∧ ((p2 ∨ True) → (p0 → p4))) → (((p4 → True) ∧ (p5 → False)) ∧ ((p5 ∧ p1) ∨ (p2 ∧ p5)))) ∨ ((((p2 → False) ∧ (p3 → p4)) ∨ ((p1 ∨ p4) ∧ (p1 ∨ p1))) → False)) := by
  apply Or.inl
  intro assump_12
  apply And.intro
  apply And.intro
  intro assump_13
  apply True.intro
  intro assump_14
  cases assump_12
  case intro assump_17 assump_18 =>
    have assump_41 : (True ∨ p7) := by
      apply Or.inl
      apply True.intro
    let assump_25 := assump_17 assump_41
    apply False.elim assump_25
  cases assump_12
  case intro assump_29 assump_30 =>
    have assump_42 : (True ∨ p7) := by
      apply Or.inl
      apply True.intro
    let assump_37 := assump_29 assump_42
    apply False.elim assump_37


variable (p7 p2 p3 p1 p0 p6 p5 : Prop)
theorem file73_211756 : ((((((p5 ∧ p0) → False) ∧ ((False ∧ p7) ∧ (p3 ∨ p5))) → (((p6 → False) → (p6 ∧ p1)) ∧ ((p3 ∨ p2) ∨ (p6 ∧ p6)))) → False) → False) := by
  intro assump_16
  have assump_59 : ((((p5 ∧ p0) → False) ∧ ((False ∧ p7) ∧ (p3 ∨ p5))) → (((p6 → False) → (p6 ∧ p1)) ∧ ((p3 ∨ p2) ∨ (p6 ∧ p6)))) := by
    intro assump_20
    apply And.intro
    intro assump_21
    apply And.intro
    cases assump_20
    case intro assump_24 assump_25 =>
      cases assump_25
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          apply False.elim assump_30
    cases assump_20
    case intro assump_36 assump_37 =>
      cases assump_37
      case intro assump_40 assump_41 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          apply False.elim assump_42
    cases assump_20
    case intro assump_46 assump_47 =>
      cases assump_47
      case intro assump_50 assump_51 =>
        cases assump_50
        case intro assump_52 assump_53 =>
          apply False.elim assump_52
  let assump_19 := assump_16 assump_59
  apply False.elim assump_19


variable (p4 p3 p6 p1 p0 p5 p2 : Prop)
theorem file73_212925 : (((((False ∧ p4) → (p0 → p3)) → False) ∧ (((p1 ∧ p2) ∧ (p6 → p5)) ∨ ((False → p3) ∨ (p5 ∧ p6)))) → False) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_14
    case inl assump_17 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          have assump_81 : ((False ∧ p4) → (p0 → p3)) := by
            intro assump_33
            intro assump_34
            cases assump_33
            case intro assump_37 assump_38 =>
              apply False.elim assump_37
          let assump_32 := assump_13 assump_81
          apply False.elim assump_32
    case inr assump_18 =>
      cases assump_18
      case inl assump_44 =>
        have assump_82 : ((False ∧ p4) → (p0 → p3)) := by
          intro assump_50
          intro assump_51
          cases assump_50
          case intro assump_54 assump_55 =>
            apply False.elim assump_54
        let assump_49 := assump_13 assump_82
        apply False.elim assump_49
      case inr assump_45 =>
        cases assump_45
        case intro assump_61 assump_62 =>
          have assump_83 : ((False ∧ p4) → (p0 → p3)) := by
            intro assump_70
            intro assump_71
            cases assump_70
            case intro assump_74 assump_75 =>
              apply False.elim assump_74
          let assump_69 := assump_13 assump_83
          apply False.elim assump_69


variable (p7 p4 p1 p0 p6 p5 : Prop)
theorem file73_214442 : ((((((True → p0) ∧ (p1 → False)) → ((p7 ∨ False) ∨ (p5 ∧ p7))) ∨ (((p4 ∨ False) ∨ (p7 → p0)) ∧ ((p5 ∧ p5) → False))) ∧ ((((p6 ∧ p7) → (False → False)) ∨ ((p4 ∨ p4) → (p6 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_54 : (((p6 ∧ p7) → (False → False)) ∨ ((p4 ∨ p4) → (p6 → False))) := by
        apply Or.inl
        intro assump_11
        intro assump_12
        apply False.elim assump_12
      let assump_10 := assump_3 assump_54
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_18 assump_19 =>
        cases assump_18
        case inl assump_20 =>
          cases assump_20
          case inl assump_22 =>
            have assump_55 : (((p6 ∧ p7) → (False → False)) ∨ ((p4 ∨ p4) → (p6 → False))) := by
              apply Or.inl
              intro assump_31
              intro assump_32
              apply False.elim assump_32
            let assump_30 := assump_3 assump_55
            apply False.elim assump_30
          case inr assump_23 =>
            apply False.elim assump_23
        case inr assump_21 =>
          have assump_56 : (((p6 ∧ p7) → (False → False)) ∨ ((p4 ∨ p4) → (p6 → False))) := by
            apply Or.inl
            intro assump_47
            intro assump_48
            apply False.elim assump_48
          let assump_46 := assump_3 assump_56
          apply False.elim assump_46


variable (p4 p5 p0 p2 p3 p7 p6 : Prop)
theorem file73_215999 : (((((p4 → p4) ∧ (p6 → False)) ∧ ((p6 ∧ False) → (p0 ∨ p5))) ∧ (((p0 ∧ False) → False) ∨ ((p3 ∨ True) ∧ (p4 → p6)))) → ((((True → False) ∧ (p0 → p7)) ∧ ((p5 ∧ p2) → (p5 ∧ p0))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_14
            case inl assump_25 =>
              have assump_72 : True := by
                apply True.intro
              let assump_35 := assump_5 assump_72
              apply False.elim assump_35
            case inr assump_26 =>
              cases assump_26
              case intro assump_39 assump_40 =>
                cases assump_39
                case inl assump_41 =>
                  have assump_73 : True := by
                    apply True.intro
                  let assump_54 := assump_5 assump_73
                  apply False.elim assump_54
                case inr assump_42 =>
                  have assump_74 : True := by
                    apply True.intro
                  let assump_68 := assump_5 assump_74
                  apply False.elim assump_68


variable (p4 p2 p6 p5 p1 p0 p3 p7 : Prop)
theorem file73_217406 : ((((((p4 ∧ p2) → (p3 ∨ p0)) ∨ ((p5 ∧ p0) ∧ (p7 → p4))) → (((p5 ∧ p3) ∨ (True ∨ p5)) ∨ ((p1 ∨ p7) ∧ (p6 ∨ p7)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p4 ∧ p2) → (p3 ∨ p0)) ∨ ((p5 ∧ p0) ∧ (p7 → p4))) → (((p5 ∧ p3) ∨ (True ∨ p5)) ∨ ((p1 ∨ p7) ∧ (p6 ∨ p7)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply Or.inr
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply Or.inl
          apply Or.inr
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p4 : Prop)
theorem file73_218195 : ((((((p4 → True) ∧ (False ∨ True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p4 → True) ∧ (False ∨ True)) → False) → False) := by
    intro assump_5
    have assump_17 : ((p4 → True) ∧ (False ∨ True)) := by
      apply And.intro
      intro assump_9
      apply True.intro
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


