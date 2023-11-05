variable (p0 p7 p6 p4 p1 p2 p3 p5 : Prop)
theorem file89_50 : (((((False → p4) → False) → ((p7 ∧ p0) → (p0 ∧ p6))) ∧ (((p0 ∧ p7) ∧ (p5 → False)) → ((p7 ∨ p1) ∧ (p2 ∨ True)))) ∨ ((((False ∧ True) ∨ (p3 ∧ p5)) ∧ ((p5 → p0) ∨ (p7 ∨ p0))) → False)) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    exact assump_4
  cases assump_2
  case intro assump_11 assump_12 =>
    have assump_47 : (False → p4) := by
      intro assump_20
      apply False.elim assump_20
    let assump_19 := assump_1 assump_47
    apply False.elim assump_19
  intro assump_26
  apply And.intro
  cases assump_26
  case intro assump_27 assump_28 =>
    cases assump_27
    case intro assump_29 assump_30 =>
      apply Or.inl
      exact assump_30
  cases assump_26
  case intro assump_37 assump_38 =>
    cases assump_37
    case intro assump_39 assump_40 =>
      apply Or.inr
      apply True.intro


variable (p0 p5 p2 p6 p1 p4 p7 : Prop)
theorem file89_1019 : (((((p4 → p0) ∧ (p0 ∧ False)) → False) ∨ (((p0 → False) ∧ (True ∨ False)) → False)) → ((((p5 ∧ p2) ∧ (True → False)) → ((p0 → False) → (p6 ∨ p7))) ∨ (((p1 → False) → False) ∨ ((False → False) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        have assump_44 : True := by
          apply True.intro
        let assump_20 := assump_11 assump_44
        apply False.elim assump_20
  case inr assump_3 =>
    apply Or.inl
    intro assump_26
    intro assump_27
    cases assump_26
    case intro assump_30 assump_31 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        have assump_45 : True := by
          apply True.intro
        let assump_40 := assump_31 assump_45
        apply False.elim assump_40


variable (p4 p5 p3 p0 p2 p7 p6 : Prop)
theorem file89_2009 : (((((p0 → p2) → False) → ((False → False) → (True ∨ p7))) ∨ (((p0 ∧ p7) ∨ (False → False)) → False)) → ((((p5 → True) → False) → ((p5 → p3) → False)) ∨ (((True ∨ p4) ∧ (p6 ∧ True)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    have assump_30 : (p5 → True) := by
      intro assump_13
      apply True.intro
    let assump_12 := assump_6 assump_30
    apply False.elim assump_12
  case inr assump_3 =>
    apply Or.inl
    intro assump_19
    intro assump_20
    have assump_31 : (p5 → True) := by
      intro assump_26
      apply True.intro
    let assump_25 := assump_19 assump_31
    apply False.elim assump_25


variable (p0 p4 p1 p2 p5 p3 : Prop)
theorem file89_2770 : (((((p3 → p3) ∧ (p4 ∨ p4)) → False) → (((False → True) → (False → p0)) ∨ ((False ∧ p5) → False))) ∨ ((((p1 → False) → (p2 → p4)) ∨ ((p5 ∧ p5) → False)) ∨ (((True → p4) ∨ (p2 → p1)) → ((p2 → False) ∧ (p1 ∨ p2))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p3 p2 p4 p6 p0 p5 p7 p1 : Prop)
theorem file89_3164 : (((((p0 → False) ∧ (p7 ∧ p3)) ∨ ((p0 → p6) ∨ (p4 → False))) → False) → ((((p1 ∨ p3) ∨ (p5 ∧ p1)) → ((True → False) → False)) ∨ (((p4 ∨ p2) ∧ (p6 → p0)) → ((p2 ∧ p4) → False)))) := by
  intro assump_11
  apply Or.inl
  intro assump_14
  intro assump_15
  cases assump_14
  case inl assump_18 =>
    cases assump_18
    case inl assump_20 =>
      have assump_48 : True := by
        apply True.intro
      let assump_25 := assump_15 assump_48
      apply False.elim assump_25
    case inr assump_21 =>
      have assump_49 : True := by
        apply True.intro
      let assump_32 := assump_15 assump_49
      apply False.elim assump_32
  case inr assump_19 =>
    cases assump_19
    case intro assump_36 assump_37 =>
      have assump_50 : True := by
        apply True.intro
      let assump_44 := assump_15 assump_50
      apply False.elim assump_44


variable (p4 p7 p1 p3 p0 p2 p6 : Prop)
theorem file89_4080 : (((((p3 → True) → False) → False) ∨ (((p6 → False) → False) ∨ ((p4 → True) ∨ (p1 ∨ p2)))) ∧ ((((p2 ∧ p7) ∧ (p3 ∨ True)) → ((p2 → False) → (p0 → p7))) ∨ (((p1 ∧ p7) → False) ∧ ((p1 → False) → (p3 → False))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  have assump_30 : (p3 → True) := by
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4
  apply Or.inl
  intro assump_9
  intro assump_10
  intro assump_11
  cases assump_9
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_17
      case inl assump_24 =>
        exact assump_19
      case inr assump_25 =>
        exact assump_19


variable (p4 p0 p2 p5 p3 p1 p6 : Prop)
theorem file89_4854 : (((((p0 ∨ p1) → False) ∧ ((p1 ∧ p4) → (False → False))) ∨ (((p1 → False) ∧ (p5 → False)) ∧ ((p3 → False) ∨ (p6 → False)))) → ((((False ∧ p2) → False) ∨ ((p0 → False) ∧ (p5 → False))) ∨ (((False → False) ∨ (p1 → p0)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply Or.inl
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  case inr assump_3 =>
    cases assump_3
    case intro assump_15 assump_16 =>
      cases assump_15
      case intro assump_17 assump_18 =>
        cases assump_16
        case inl assump_23 =>
          apply Or.inl
          apply Or.inl
          intro assump_27
          cases assump_27
          case intro assump_28 assump_29 =>
            apply False.elim assump_28
        case inr assump_24 =>
          apply Or.inl
          apply Or.inl
          intro assump_34
          cases assump_34
          case intro assump_35 assump_36 =>
            apply False.elim assump_35


variable (p0 p3 p7 p4 p6 p5 p1 : Prop)
theorem file89_6007 : (((((p3 ∨ p3) ∧ (p4 ∧ p1)) ∧ ((p0 ∨ p4) → (p5 → p4))) ∨ (((True ∨ p0) ∨ (True ∧ p5)) ∨ ((False → p1) ∧ (p5 ∨ p4)))) ∨ ((((False ∨ p1) ∨ (p3 ∨ True)) ∨ ((p6 → p7) → False)) → False)) := by
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p6 p3 p7 p4 p0 p2 p5 : Prop)
theorem file89_6352 : ((((((p0 → p4) → (False ∧ p6)) → ((p5 ∧ p7) → False)) ∨ (((p3 → False) ∧ (p6 → False)) → ((p3 → False) ∨ (True → False)))) ∧ ((((True → False) ∧ (False → p2)) → ((p5 ∧ p7) ∧ (False → False))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      have assump_78 : (((True → False) ∧ (False → p2)) → ((p5 ∧ p7) ∧ (False → False))) := by
        intro assump_15
        apply And.intro
        apply And.intro
        cases assump_15
        case intro assump_16 assump_17 =>
          have assump_79 : True := by
            apply True.intro
          let assump_23 := assump_16 assump_79
          apply False.elim assump_23
        cases assump_15
        case intro assump_27 assump_28 =>
          have assump_80 : True := by
            apply True.intro
          let assump_34 := assump_27 assump_80
          apply False.elim assump_34
        intro assump_38
        apply False.elim assump_38
      let assump_14 := assump_7 assump_78
      apply False.elim assump_14
    case inr assump_9 =>
      have assump_81 : (((True → False) ∧ (False → p2)) → ((p5 ∧ p7) ∧ (False → False))) := by
        intro assump_49
        apply And.intro
        apply And.intro
        cases assump_49
        case intro assump_50 assump_51 =>
          have assump_82 : True := by
            apply True.intro
          let assump_57 := assump_50 assump_82
          apply False.elim assump_57
        cases assump_49
        case intro assump_61 assump_62 =>
          have assump_83 : True := by
            apply True.intro
          let assump_68 := assump_61 assump_83
          apply False.elim assump_68
        intro assump_72
        apply False.elim assump_72
      let assump_48 := assump_7 assump_81
      apply False.elim assump_48


variable (p1 p5 p7 p0 p4 p3 p2 : Prop)
theorem file89_8239 : ((((((True → False) ∧ (False → p7)) → ((p0 ∨ p1) ∨ (p4 ∧ p1))) → False) ∧ ((((p2 ∨ p3) ∨ (False → p1)) ∨ ((False ∨ p5) → (p1 ∧ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p2 ∨ p3) ∨ (False → p1)) ∨ ((False ∨ p5) → (p1 ∧ p5))) := by
      apply Or.inl
      apply Or.inr
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p7 p0 p4 p3 p1 p2 p6 : Prop)
theorem file89_8773 : ((((((p7 ∨ p0) ∧ (p4 → False)) → False) → (((p0 → p3) → (p4 ∨ False)) → ((p6 → False) ∧ (p2 ∧ False)))) ∧ ((((True → p0) ∨ (p6 → False)) ∧ ((False ∨ p6) ∧ (p7 ∨ True))) ∧ (((False ∧ p2) ∧ (p2 ∨ p1)) ∧ ((p7 ∧ p0) ∧ (p4 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              apply False.elim assump_16
            case inr assump_17 =>
              cases assump_15
              case inl assump_22 =>
                cases assump_7
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case intro assump_30 assump_31 =>
                      apply False.elim assump_30
              case inr assump_23 =>
                cases assump_7
                case intro assump_36 assump_37 =>
                  cases assump_36
                  case intro assump_38 assump_39 =>
                    cases assump_38
                    case intro assump_40 assump_41 =>
                      apply False.elim assump_40
        case inr assump_11 =>
          cases assump_9
          case intro assump_46 assump_47 =>
            cases assump_46
            case inl assump_48 =>
              apply False.elim assump_48
            case inr assump_49 =>
              cases assump_47
              case inl assump_54 =>
                cases assump_7
                case intro assump_58 assump_59 =>
                  cases assump_58
                  case intro assump_60 assump_61 =>
                    cases assump_60
                    case intro assump_62 assump_63 =>
                      apply False.elim assump_62
              case inr assump_55 =>
                cases assump_7
                case intro assump_68 assump_69 =>
                  cases assump_68
                  case intro assump_70 assump_71 =>
                    cases assump_70
                    case intro assump_72 assump_73 =>
                      apply False.elim assump_72


variable (p7 p4 p3 p2 : Prop)
theorem file89_11178 : (((((True ∨ p2) → (False → p7)) ∨ ((p2 → p4) → (p7 ∨ p3))) → False) → False) := by
  intro assump_1
  have assump_12 : (((True ∨ p2) → (False → p7)) ∨ ((p2 → p4) → (p7 ∨ p3))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p1 p7 p6 p3 p5 p4 p2 p0 : Prop)
theorem file89_11576 : ((((((p1 → True) ∧ (p2 ∧ p6)) → ((p4 ∧ p5) → (p0 → p3))) → False) ∧ ((((p0 → p1) ∨ (True ∨ p2)) → ((p0 → p7) → (True ∨ p6))) → (((False → p6) ∧ (False → p3)) → False))) → False) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    have assump_42 : (((p0 → p1) ∨ (True ∨ p2)) → ((p0 → p7) → (True ∨ p6))) := by
      intro assump_18
      intro assump_19
      cases assump_18
      case inl assump_22 =>
        apply Or.inl
        apply True.intro
      case inr assump_23 =>
        cases assump_23
        case inl assump_26 =>
          apply Or.inl
          apply True.intro
        case inr assump_27 =>
          apply Or.inl
          apply True.intro
    let assump_17 := assump_12 assump_42
    have assump_43 : ((False → p6) ∧ (False → p3)) := by
      apply And.intro
      intro assump_33
      apply False.elim assump_33
      intro assump_36
      apply False.elim assump_36
    let assump_32 := assump_17 assump_43
    apply False.elim assump_32


variable (p7 p5 p0 p6 p3 p4 p1 p2 : Prop)
theorem file89_12635 : (((((p3 ∧ p7) → False) ∧ ((p4 ∨ False) ∨ (p2 ∧ p0))) ∧ (((True → False) → (p5 ∧ True)) → ((p7 → p3) ∨ (p2 → True)))) → ((((p5 → True) → (p1 → False)) ∧ ((True ∧ p3) → (p0 → p0))) → (((p0 ∨ p3) ∨ (p0 ∧ p4)) → ((p1 ∧ p6) → (False → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p6 p5 p0 p3 : Prop)
theorem file89_13049 : ((((((p6 → p6) → False) → False) ∨ (((p3 → False) → False) ∧ ((p0 → True) → (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p6 → p6) → False) → False) ∨ (((p3 → False) → False) ∧ ((p0 → True) → (p5 → False)))) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (p6 → p6) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p3 p6 p0 p5 : Prop)
theorem file89_13603 : ((((((p5 ∧ p0) ∧ (p1 ∧ p1)) → ((p6 → False) ∧ (p0 → False))) → (((False ∨ p3) ∧ (p1 ∧ p6)) → ((p1 → True) ∧ (p5 → True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p5 ∧ p0) ∧ (p1 ∧ p1)) → ((p6 → False) ∧ (p0 → False))) → (((False ∨ p3) ∧ (p1 ∧ p6)) → ((p1 → True) ∧ (p5 → True)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    apply True.intro
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p4 p3 p1 p0 p6 p5 p7 : Prop)
theorem file89_14182 : (((((p4 → p2) ∨ (p0 ∧ p5)) ∨ ((p1 ∧ p7) ∧ (True → False))) → (((False → True) → (p0 → False)) ∨ ((p3 ∧ p0) → (False ∧ False)))) → ((((p0 ∨ p0) ∧ (False ∧ p0)) ∧ ((p1 ∨ p1) ∨ (p7 ∨ p3))) → (((p0 → p1) ∨ (p6 → True)) ∨ ((p1 → p6) → (p3 → p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_6
        case intro assump_11 assump_12 =>
          apply False.elim assump_11
      case inr assump_8 =>
        cases assump_6
        case intro assump_17 assump_18 =>
          apply False.elim assump_17


variable (p5 p1 p3 p2 p0 p4 p6 p7 : Prop)
theorem file89_14917 : ((((((False ∨ p0) ∨ (p5 → False)) → False) ∧ (((p6 ∨ p5) ∨ (p0 ∧ p1)) → False)) ∧ ((((p4 ∨ p6) ∧ (p1 ∨ p0)) → ((p0 ∨ False) ∧ (p0 → p2))) ∧ (((True ∨ p3) ∧ (p1 ∧ p5)) ∨ ((p7 ∧ p2) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_17
              case intro assump_22 assump_23 =>
                have assump_70 : ((p6 ∨ p5) ∨ (p0 ∧ p1)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_23
                let assump_31 := assump_5 assump_70
                apply False.elim assump_31
            case inr assump_19 =>
              cases assump_17
              case intro assump_37 assump_38 =>
                have assump_71 : ((p6 ∨ p5) ∨ (p0 ∧ p1)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_38
                let assump_47 := assump_5 assump_71
                apply False.elim assump_47
        case inr assump_15 =>
          have assump_72 : ((False ∨ p0) ∨ (p5 → False)) := by
            apply Or.inr
            intro assump_57
            have assump_73 : ((p6 ∨ p5) ∨ (p0 ∧ p1)) := by
              apply Or.inl
              apply Or.inr
              exact assump_57
            let assump_63 := assump_5 assump_73
            apply False.elim assump_63
          let assump_56 := assump_4 assump_72
          apply False.elim assump_56


variable (p6 p4 p1 p2 p7 p0 p3 p5 : Prop)
theorem file89_16717 : (((((False ∨ p6) ∨ (p7 ∨ True)) ∨ ((p7 → False) → False)) ∨ (((p4 → False) ∨ (p3 → p1)) → False)) ∨ ((((p1 → False) → (p0 → p7)) ∧ ((p0 ∧ p4) ∧ (p5 → False))) ∨ (((p6 ∨ p2) ∧ (False → False)) → ((p4 ∨ p1) ∧ (p7 ∨ True))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inr
  apply True.intro


variable (p6 p5 p3 p0 p4 p2 : Prop)
theorem file89_17100 : ((((((p6 ∨ p0) → False) ∨ ((p6 → False) ∨ (p6 ∧ p3))) ∧ (((p5 ∧ p3) ∨ (p2 → False)) → ((p4 → False) → False))) ∧ ((((True → False) → (p4 ∨ True)) ∨ ((p6 → False) ∨ (p5 → False))) → False)) → False) := by
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_20
      case inl assump_22 =>
        have assump_69 : (((True → False) → (p4 ∨ True)) ∨ ((p6 → False) ∨ (p5 → False))) := by
          apply Or.inl
          intro assump_31
          apply Or.inr
          apply True.intro
        let assump_30 := assump_19 assump_69
        apply False.elim assump_30
      case inr assump_23 =>
        cases assump_23
        case inl assump_37 =>
          have assump_70 : (((True → False) → (p4 ∨ True)) ∨ ((p6 → False) ∨ (p5 → False))) := by
            apply Or.inl
            intro assump_46
            apply Or.inr
            apply True.intro
          let assump_45 := assump_19 assump_70
          apply False.elim assump_45
        case inr assump_38 =>
          cases assump_38
          case intro assump_52 assump_53 =>
            have assump_71 : (((True → False) → (p4 ∨ True)) ∨ ((p6 → False) ∨ (p5 → False))) := by
              apply Or.inl
              intro assump_63
              apply Or.inr
              apply True.intro
            let assump_62 := assump_19 assump_71
            apply False.elim assump_62


variable (p7 p5 p3 p6 p1 p0 : Prop)
theorem file89_18593 : (((((False ∧ p1) → (p0 → False)) → False) → False) → ((((False → False) → False) → ((True → True) → (p5 → False))) ∨ (((p0 ∨ True) → (p6 ∨ False)) ∧ ((True ∧ True) ∧ (p3 ∨ p7))))) := by
  intro assump_6
  apply Or.inl
  intro assump_9
  intro assump_10
  intro assump_11
  have assump_25 : (False → False) := by
    intro assump_19
    apply False.elim assump_19
  let assump_18 := assump_9 assump_25
  apply False.elim assump_18


variable (p3 p6 p0 p7 p1 p4 p2 p5 : Prop)
theorem file89_19089 : (((((p2 ∧ p1) → False) ∨ ((False ∨ p4) → False)) ∧ (((p6 ∨ p5) ∨ (True → False)) → False)) → ((((p3 ∧ p6) ∧ (p7 ∧ p1)) ∧ ((p4 → False) → (p5 → p7))) → (((True ∨ False) → (p0 → p1)) → ((True → p2) ∨ (p1 ∧ p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_9
        case intro assump_16 assump_17 =>
          cases assump_1
          case intro assump_24 assump_25 =>
            cases assump_24
            case inl assump_26 =>
              apply Or.inl
              intro assump_32
              have assump_50 : ((p6 ∨ p5) ∨ (True → False)) := by
                apply Or.inl
                apply Or.inl
                exact assump_11
              let assump_35 := assump_25 assump_50
              apply False.elim assump_35
            case inr assump_27 =>
              apply Or.inl
              intro assump_43
              have assump_51 : ((p6 ∨ p5) ∨ (True → False)) := by
                apply Or.inl
                apply Or.inl
                exact assump_11
              let assump_46 := assump_25 assump_51
              apply False.elim assump_46


variable (p6 p3 p1 p7 p0 p2 p5 : Prop)
theorem file89_20428 : (((((p2 → False) ∨ (p5 → False)) → ((p3 → False) → (False → p2))) → False) → ((((p0 → False) → False) ∧ ((p7 → False) → (p6 ∧ p0))) → (((p7 ∧ p3) ∨ (p3 ∧ p0)) ∨ ((False → False) ∨ (p1 → p3))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inr
    apply Or.inl
    intro assump_11
    apply False.elim assump_11


variable (p6 p7 : Prop)
theorem file89_20846 : (((((p6 → p7) ∨ (p7 ∨ False)) → ((p6 → False) → (p6 → False))) → False) → False) := by
  intro assump_28
  have assump_63 : (((p6 → p7) ∨ (p7 ∨ False)) → ((p6 → False) → (p6 → False))) := by
    intro assump_32
    intro assump_33
    intro assump_34
    cases assump_32
    case inl assump_39 =>
      have assump_64 : p6 := by
        exact assump_34
      let assump_45 := assump_33 assump_64
      apply False.elim assump_45
    case inr assump_40 =>
      cases assump_40
      case inl assump_49 =>
        have assump_65 : p6 := by
          exact assump_34
        let assump_54 := assump_33 assump_65
        apply False.elim assump_54
      case inr assump_50 =>
        apply False.elim assump_50
  let assump_31 := assump_28 assump_63
  apply False.elim assump_31


variable (p2 p5 p7 p3 p4 p1 : Prop)
theorem file89_21682 : (((((p5 → False) → (p7 → p2)) → False) ∧ (((p4 → False) → False) ∧ ((p5 ∨ p7) ∨ (p2 ∨ p5)))) → ((((False → p2) ∨ (True → p3)) ∨ ((p3 → p5) ∨ (False ∨ p2))) ∨ (((True → p4) ∧ (p5 ∧ p1)) ∧ ((p2 → p4) → False)))) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_26
    case intro assump_29 assump_30 =>
      cases assump_30
      case inl assump_33 =>
        cases assump_33
        case inl assump_35 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_39
          apply False.elim assump_39
        case inr assump_36 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_44
          apply False.elim assump_44
      case inr assump_34 =>
        cases assump_34
        case inl assump_47 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_51
          apply False.elim assump_51
        case inr assump_48 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_56
          apply False.elim assump_56


variable (p1 p0 p6 p2 p5 : Prop)
theorem file89_22859 : (((((False → False) → False) ∧ ((False → False) → False)) → False) ∨ ((((p1 → p5) ∧ (p2 → False)) ∧ ((p6 → False) → (p6 ∨ True))) → (((p0 ∧ p2) ∧ (True ∧ p2)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p0 p2 p5 p4 p7 p3 : Prop)
theorem file89_23343 : (((((p2 → False) → False) → ((p2 → p5) → False)) ∧ (((True → False) → (True → False)) → False)) → ((((p4 → p7) ∧ (p7 → False)) → ((True ∨ False) ∨ (p5 ∧ p5))) ∨ (((p3 → p4) → False) ∨ ((p0 ∧ False) ∨ (False → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p6 p4 p5 p0 p7 p1 p2 : Prop)
theorem file89_23853 : ((((((False → False) ∧ (p1 → p0)) ∧ ((p1 ∨ p6) ∨ (p4 → p4))) ∧ (((False ∧ p0) → False) → ((p1 ∧ p7) ∧ (p5 ∧ p6)))) ∧ ((((p7 → False) ∧ (True → False)) ∨ ((p1 ∨ p1) ∧ (False ∧ p5))) ∧ (((False ∧ p2) → (p6 ∧ p1)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_7
          case inl assump_14 =>
            cases assump_14
            case inl assump_16 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_22
                case inl assump_24 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    have assump_153 : ((False ∧ p2) → (p6 ∧ p1)) := by
                      intro assump_35
                      apply And.intro
                      cases assump_35
                      case intro assump_36 assump_37 =>
                        apply False.elim assump_36
                      cases assump_35
                      case intro assump_40 assump_41 =>
                        apply False.elim assump_40
                    let assump_34 := assump_23 assump_153
                    apply False.elim assump_34
                case inr assump_25 =>
                  cases assump_25
                  case intro assump_47 assump_48 =>
                    cases assump_47
                    case inl assump_49 =>
                      cases assump_48
                      case intro assump_53 assump_54 =>
                        apply False.elim assump_53
                    case inr assump_50 =>
                      cases assump_48
                      case intro assump_59 assump_60 =>
                        apply False.elim assump_59
            case inr assump_17 =>
              cases assump_3
              case intro assump_67 assump_68 =>
                cases assump_67
                case inl assump_69 =>
                  cases assump_69
                  case intro assump_71 assump_72 =>
                    have assump_154 : ((False ∧ p2) → (p6 ∧ p1)) := by
                      intro assump_80
                      apply And.intro
                      cases assump_80
                      case intro assump_81 assump_82 =>
                        apply False.elim assump_81
                      cases assump_80
                      case intro assump_85 assump_86 =>
                        apply False.elim assump_85
                    let assump_79 := assump_68 assump_154
                    apply False.elim assump_79
                case inr assump_70 =>
                  cases assump_70
                  case intro assump_92 assump_93 =>
                    cases assump_92
                    case inl assump_94 =>
                      cases assump_93
                      case intro assump_98 assump_99 =>
                        apply False.elim assump_98
                    case inr assump_95 =>
                      cases assump_93
                      case intro assump_104 assump_105 =>
                        apply False.elim assump_104
          case inr assump_15 =>
            cases assump_3
            case intro assump_112 assump_113 =>
              cases assump_112
              case inl assump_114 =>
                cases assump_114
                case intro assump_116 assump_117 =>
                  have assump_155 : ((False ∧ p2) → (p6 ∧ p1)) := by
                    intro assump_125
                    apply And.intro
                    cases assump_125
                    case intro assump_126 assump_127 =>
                      apply False.elim assump_126
                    cases assump_125
                    case intro assump_130 assump_131 =>
                      apply False.elim assump_130
                  let assump_124 := assump_113 assump_155
                  apply False.elim assump_124
              case inr assump_115 =>
                cases assump_115
                case intro assump_137 assump_138 =>
                  cases assump_137
                  case inl assump_139 =>
                    cases assump_138
                    case intro assump_143 assump_144 =>
                      apply False.elim assump_143
                  case inr assump_140 =>
                    cases assump_138
                    case intro assump_149 assump_150 =>
                      apply False.elim assump_149


variable (p4 p0 : Prop)
theorem file89_28474 : ((((((p0 → False) → (False → p4)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p0 → False) → (False → p4)) → False) → False) := by
    intro assump_5
    have assump_20 : ((p0 → False) → (False → p4)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_5 assump_20
    apply False.elim assump_8
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p6 p4 p3 p7 p0 p5 : Prop)
theorem file89_28988 : (((((p4 ∧ p0) ∧ (p7 → False)) → ((p3 ∧ True) → False)) → False) → ((((p4 ∧ p5) → False) → ((p5 → False) ∨ (p0 ∧ True))) ∨ (((p7 ∨ True) → (p6 ∧ False)) ∧ ((p4 → p4) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inl
  intro assump_7
  have assump_43 : (((p4 ∧ p0) ∧ (p7 → False)) → ((p3 ∧ True) → False)) := by
    intro assump_13
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      cases assump_13
      case intro assump_21 assump_22 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          have assump_44 : (p4 ∧ p5) := by
            apply And.intro
            exact assump_23
            exact assump_7
          let assump_36 := assump_4 assump_44
          apply False.elim assump_36
  let assump_12 := assump_1 assump_43
  apply False.elim assump_12


variable (p6 p4 p0 p7 p5 p1 : Prop)
theorem file89_29892 : (((((p6 ∨ p0) ∧ (p6 ∧ p4)) ∧ ((True ∨ p5) → (p5 ∧ p7))) ∧ (((True ∧ p1) → False) ∧ ((p5 ∨ p4) → False))) → False) := by
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
          case intro assump_12 assump_13 =>
            cases assump_3
            case intro assump_20 assump_21 =>
              have assump_50 : (p5 ∨ p4) := by
                apply Or.inr
                exact assump_13
              let assump_26 := assump_21 assump_50
              apply False.elim assump_26
        case inr assump_9 =>
          cases assump_7
          case intro assump_32 assump_33 =>
            cases assump_3
            case intro assump_40 assump_41 =>
              have assump_51 : (p5 ∨ p4) := by
                apply Or.inr
                exact assump_33
              let assump_46 := assump_41 assump_51
              apply False.elim assump_46


variable (p2 p3 p0 p4 p1 : Prop)
theorem file89_31016 : ((((((True → False) → (p4 ∨ True)) ∨ ((p1 ∨ p3) ∨ (p4 → p3))) ∨ (((p0 → p2) → (p3 ∨ True)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((True → False) → (p4 ∨ True)) ∨ ((p1 ∨ p3) ∨ (p4 → p3))) ∨ (((p0 → p2) → (p3 ∨ True)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p4 p7 p3 : Prop)
theorem file89_31492 : (((((p4 ∧ False) → False) → False) → False) ∨ ((((p4 ∨ p0) → False) ∧ ((p0 ∨ p3) ∧ (p7 → False))) → (((p0 ∧ p3) ∧ (p7 ∧ True)) ∨ ((True ∧ p4) → (p4 → p4))))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((p4 ∧ False) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p4 p7 p3 p0 p5 : Prop)
theorem file89_31967 : (((((p7 ∨ p3) → (False ∧ p2)) ∧ ((False ∧ p0) ∧ (True ∧ False))) → (((p7 → False) → (p4 → False)) ∨ ((p7 ∨ p5) → (p4 ∨ True)))) ∧ ((((p5 ∧ p4) → (False → False)) → False) → False)) := by
  apply And.intro
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_13
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        apply False.elim assump_18
  intro assump_22
  have assump_33 : ((p5 ∧ p4) → (False → False)) := by
    intro assump_26
    intro assump_27
    apply False.elim assump_27
  let assump_25 := assump_22 assump_33
  apply False.elim assump_25


variable (p7 p4 p6 p1 p0 p5 : Prop)
theorem file89_32671 : (((((False → p5) → False) → False) ∨ (((p4 → False) → (p4 → False)) → False)) ∨ ((((p0 → p4) → (False → False)) → False) → (((p6 ∧ p0) → False) → ((p1 ∧ p6) ∨ (p7 ∨ False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (False → p5) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p5 p2 p0 p4 : Prop)
theorem file89_33109 : ((((((p0 ∧ p4) ∧ (p7 ∨ p7)) → False) ∨ (((p2 → False) ∧ (p5 → False)) → False)) ∧ ((((False → False) ∨ (False ∨ False)) ∨ ((p5 → False) ∧ (p0 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_28 : (((False → False) ∨ (False ∨ False)) ∨ ((p5 → False) ∧ (p0 → False))) := by
        apply Or.inl
        apply Or.inl
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_3 assump_28
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_29 : (((False → False) ∨ (False ∨ False)) ∨ ((p5 → False) ∧ (p0 → False))) := by
        apply Or.inl
        apply Or.inl
        intro assump_22
        apply False.elim assump_22
      let assump_21 := assump_3 assump_29
      apply False.elim assump_21


variable (p5 p3 p2 p4 : Prop)
theorem file89_34028 : ((((((p3 ∧ True) → (p3 ∨ p2)) ∨ ((p4 ∨ p4) ∨ (False ∧ False))) → False) ∨ ((((p3 ∧ p5) → (p5 → p3)) → False) ∧ (((p2 → False) → (False ∨ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_30 : (((p3 ∧ True) → (p3 ∨ p2)) ∨ ((p4 ∨ p4) ∨ (False ∧ False))) := by
      apply Or.inl
      intro assump_7
      cases assump_7
      case intro assump_8 assump_9 =>
        apply Or.inl
        exact assump_8
    let assump_6 := assump_2 assump_30
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_17 assump_18 =>
      have assump_31 : ((p2 → False) → (False ∨ True)) := by
        intro assump_24
        apply Or.inr
        apply True.intro
      let assump_23 := assump_18 assump_31
      apply False.elim assump_23


variable (p6 p4 p0 p3 p1 p2 : Prop)
theorem file89_34901 : (((((False → p3) → False) ∧ ((p2 ∧ p1) → False)) ∧ (((False ∧ p1) ∧ (p6 → False)) → False)) → ((((p4 → False) → False) ∨ ((p0 ∨ p0) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        have assump_47 : (False → p3) := by
          intro assump_20
          apply False.elim assump_20
        let assump_19 := assump_9 assump_47
        apply False.elim assump_19
  case inr assump_4 =>
    cases assump_1
    case intro assump_28 assump_29 =>
      cases assump_28
      case intro assump_30 assump_31 =>
        have assump_48 : (False → p3) := by
          intro assump_41
          apply False.elim assump_41
        let assump_40 := assump_30 assump_48
        apply False.elim assump_40


variable (p0 p7 p3 p4 p5 p1 p2 p6 : Prop)
theorem file89_35829 : (((((True ∨ p6) → (True → False)) → ((True ∧ p6) → (p0 ∧ p2))) ∨ (((p5 ∧ p4) → False) ∨ ((True → False) → (p3 → p0)))) ∨ ((((p6 ∨ p1) ∨ (p2 → p1)) → ((p4 → False) ∨ (p7 → False))) → (((p7 → False) → (p2 ∧ False)) ∨ ((p6 → p0) → (p5 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_29 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_11 := assump_1 assump_29
    have assump_30 : True := by
      apply True.intro
    let assump_12 := assump_11 assump_30
    apply False.elim assump_12
  cases assump_2
  case intro assump_16 assump_17 =>
    have assump_31 : (True ∨ p6) := by
      apply Or.inl
      apply True.intro
    let assump_24 := assump_1 assump_31
    have assump_32 : True := by
      apply True.intro
    let assump_25 := assump_24 assump_32
    apply False.elim assump_25


variable (p1 p5 p3 p4 p7 p0 p6 : Prop)
theorem file89_36825 : (((((p4 ∨ True) → False) ∧ ((p0 ∨ p5) → (p1 ∧ p3))) → False) ∨ ((((p0 ∨ p0) → (False → False)) → ((p3 → p6) ∨ (p6 ∨ p1))) ∧ (((True → p0) ∧ (False → p0)) ∧ ((p7 ∨ p5) → (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (p4 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_9 := assump_2 assump_13
    apply False.elim assump_9


variable (p4 p1 p0 p7 p3 p6 p5 : Prop)
theorem file89_37313 : (((((False → False) → False) ∧ ((p0 → p7) ∧ (p0 ∨ p3))) → False) ∨ ((((p5 ∧ p4) ∧ (p7 ∨ p0)) → False) → (((p3 → False) → False) → ((p6 ∧ p1) → (True → p6))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_35 : (False → False) := by
          intro assump_18
          apply False.elim assump_18
        let assump_17 := assump_2 assump_35
        apply False.elim assump_17
      case inr assump_11 =>
        have assump_36 : (False → False) := by
          intro assump_29
          apply False.elim assump_29
        let assump_28 := assump_2 assump_36
        apply False.elim assump_28


variable (p1 p2 p0 p4 p3 p6 p7 p5 : Prop)
theorem file89_38137 : (((((p5 → False) → False) → False) → (((p5 → p2) ∨ (p2 → False)) ∨ ((p1 → False) → (p7 ∧ p6)))) ∨ ((((p3 → False) → (False ∧ p7)) ∨ ((p5 ∨ p6) ∧ (p2 ∨ False))) ∧ (((p3 ∧ p3) → (p0 → False)) ∨ ((True ∨ p2) ∨ (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_19 : ((p5 → False) → False) := by
    intro assump_9
    have assump_20 : p5 := by
      exact assump_4
    let assump_12 := assump_9 assump_20
    apply False.elim assump_12
  let assump_8 := assump_1 assump_19
  apply False.elim assump_8


variable (p7 p2 p3 p4 p1 p6 p0 p5 : Prop)
theorem file89_38766 : (((((p6 ∨ False) → False) → ((p0 ∨ p3) → (p2 ∨ p2))) → (((p0 → False) ∧ (False ∧ p3)) → ((p2 → False) → False))) ∨ ((((p5 → False) ∧ (p7 → False)) → ((p1 → False) ∧ (p4 ∧ p0))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      apply False.elim assump_10


variable (p3 p5 p1 p0 p2 p6 p7 p4 : Prop)
theorem file89_39232 : (((((p3 ∧ p5) → False) → ((p2 → False) ∧ (p0 ∨ p7))) → (((False ∨ p5) → (p5 ∨ p5)) → ((p2 ∧ p6) → (p6 ∨ p1)))) ∨ ((((p4 ∨ p0) → False) ∨ ((p5 ∧ p1) ∧ (p7 → p6))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply Or.inl
    exact assump_5


variable (p3 p6 p1 p7 p2 p4 : Prop)
theorem file89_39623 : (((((True ∨ p2) ∨ (p6 → False)) ∧ ((p7 ∨ p3) → False)) ∧ (((p3 ∨ p4) → False) ∧ ((p4 ∨ p7) ∨ (p1 ∧ p4)))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            cases assump_19
            case inl assump_22 =>
              cases assump_22
              case inl assump_24 =>
                have assump_131 : (p3 ∨ p4) := by
                  apply Or.inr
                  exact assump_24
                let assump_29 := assump_18 assump_131
                apply False.elim assump_29
              case inr assump_25 =>
                have assump_132 : (p7 ∨ p3) := by
                  apply Or.inl
                  exact assump_25
                let assump_37 := assump_9 assump_132
                apply False.elim assump_37
            case inr assump_23 =>
              cases assump_23
              case intro assump_41 assump_42 =>
                have assump_133 : (p3 ∨ p4) := by
                  apply Or.inr
                  exact assump_42
                let assump_49 := assump_18 assump_133
                apply False.elim assump_49
        case inr assump_13 =>
          cases assump_7
          case intro assump_57 assump_58 =>
            cases assump_58
            case inl assump_61 =>
              cases assump_61
              case inl assump_63 =>
                have assump_134 : (p3 ∨ p4) := by
                  apply Or.inr
                  exact assump_63
                let assump_68 := assump_57 assump_134
                apply False.elim assump_68
              case inr assump_64 =>
                have assump_135 : (p7 ∨ p3) := by
                  apply Or.inl
                  exact assump_64
                let assump_76 := assump_9 assump_135
                apply False.elim assump_76
            case inr assump_62 =>
              cases assump_62
              case intro assump_80 assump_81 =>
                have assump_136 : (p3 ∨ p4) := by
                  apply Or.inr
                  exact assump_81
                let assump_88 := assump_57 assump_136
                apply False.elim assump_88
      case inr assump_11 =>
        cases assump_7
        case intro assump_96 assump_97 =>
          cases assump_97
          case inl assump_100 =>
            cases assump_100
            case inl assump_102 =>
              have assump_137 : (p3 ∨ p4) := by
                apply Or.inr
                exact assump_102
              let assump_107 := assump_96 assump_137
              apply False.elim assump_107
            case inr assump_103 =>
              have assump_138 : (p7 ∨ p3) := by
                apply Or.inl
                exact assump_103
              let assump_115 := assump_9 assump_138
              apply False.elim assump_115
          case inr assump_101 =>
            cases assump_101
            case intro assump_119 assump_120 =>
              have assump_139 : (p3 ∨ p4) := by
                apply Or.inr
                exact assump_120
              let assump_127 := assump_96 assump_139
              apply False.elim assump_127


variable (p2 p6 p3 p1 : Prop)
theorem file89_42989 : (((((p1 ∨ True) ∧ (p6 ∧ False)) → ((p2 ∧ p1) ∨ (False → p3))) → False) → ((((p6 ∧ p6) → (True ∨ p1)) ∧ ((p6 → True) ∧ (p1 → True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      have assump_40 : (((p1 ∨ True) ∧ (p6 ∧ False)) → ((p2 ∧ p1) ∨ (False → p3))) := by
        intro assump_16
        cases assump_16
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            cases assump_18
            case intro assump_23 assump_24 =>
              apply False.elim assump_24
          case inr assump_20 =>
            cases assump_18
            case intro assump_31 assump_32 =>
              apply False.elim assump_32
      let assump_15 := assump_1 assump_40
      apply False.elim assump_15


variable (p4 p2 p1 p5 p7 p3 : Prop)
theorem file89_43911 : ((((((p1 ∨ p4) → False) → False) ∨ (((p3 ∧ True) → False) ∨ ((p5 ∨ True) ∧ (p7 → False)))) ∧ ((((p3 ∧ p2) → (p3 ∧ p3)) → False) ∧ (((p2 ∧ p7) ∧ (p4 → p4)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_120 : ((p3 ∧ p2) → (p3 ∧ p3)) := by
          intro assump_16
          apply And.intro
          cases assump_16
          case intro assump_17 assump_18 =>
            exact assump_17
          cases assump_16
          case intro assump_23 assump_24 =>
            exact assump_23
        let assump_15 := assump_8 assump_120
        apply False.elim assump_15
    case inr assump_5 =>
      cases assump_5
      case inl assump_32 =>
        cases assump_3
        case intro assump_36 assump_37 =>
          have assump_121 : ((p3 ∧ p2) → (p3 ∧ p3)) := by
            intro assump_44
            apply And.intro
            cases assump_44
            case intro assump_45 assump_46 =>
              exact assump_45
            cases assump_44
            case intro assump_51 assump_52 =>
              exact assump_51
          let assump_43 := assump_36 assump_121
          apply False.elim assump_43
      case inr assump_33 =>
        cases assump_33
        case intro assump_60 assump_61 =>
          cases assump_60
          case inl assump_62 =>
            cases assump_3
            case intro assump_68 assump_69 =>
              have assump_122 : ((p3 ∧ p2) → (p3 ∧ p3)) := by
                intro assump_76
                apply And.intro
                cases assump_76
                case intro assump_77 assump_78 =>
                  exact assump_77
                cases assump_76
                case intro assump_83 assump_84 =>
                  exact assump_83
              let assump_75 := assump_68 assump_122
              apply False.elim assump_75
          case inr assump_63 =>
            cases assump_3
            case intro assump_96 assump_97 =>
              have assump_123 : ((p3 ∧ p2) → (p3 ∧ p3)) := by
                intro assump_104
                apply And.intro
                cases assump_104
                case intro assump_105 assump_106 =>
                  exact assump_105
                cases assump_104
                case intro assump_111 assump_112 =>
                  exact assump_111
              let assump_103 := assump_96 assump_123
              apply False.elim assump_103


variable (p4 p3 p6 p7 : Prop)
theorem file89_46490 : ((((((p6 ∧ p3) ∧ (p6 ∨ False)) → ((True → False) → (False → False))) ∨ (((True ∧ p4) ∧ (True → False)) ∧ ((p6 ∧ p3) ∨ (p7 → True)))) → False) → False) := by
  intro assump_39
  have assump_51 : ((((p6 ∧ p3) ∧ (p6 ∨ False)) → ((True → False) → (False → False))) ∨ (((True ∧ p4) ∧ (True → False)) ∧ ((p6 ∧ p3) ∨ (p7 → True)))) := by
    apply Or.inl
    intro assump_43
    intro assump_44
    intro assump_45
    apply False.elim assump_45
  let assump_42 := assump_39 assump_51
  apply False.elim assump_42


variable (p1 p3 p4 p7 p6 p0 p2 p5 : Prop)
theorem file89_47063 : (((((True → False) ∧ (p3 ∨ p7)) → False) ∨ (((p3 ∨ p0) → False) → False)) ∨ ((((p3 → p0) ∨ (p2 → True)) ∨ ((p4 ∧ p0) ∧ (p1 ∧ p4))) ∧ (((p5 ∨ p0) → False) → ((p5 → p3) ∧ (p6 ∨ p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_22 : True := by
        apply True.intro
      let assump_11 := assump_2 assump_22
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_23 : True := by
        apply True.intro
      let assump_18 := assump_2 assump_23
      apply False.elim assump_18


variable (p3 p2 p7 p5 p0 p6 : Prop)
theorem file89_47747 : ((((((p6 → True) → False) → ((p5 ∧ p2) ∨ (p7 → False))) ∨ (((p3 → False) → False) → ((p0 ∧ True) → False))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p6 → True) → False) → ((p5 ∧ p2) ∨ (p7 → False))) ∨ (((p3 → False) → False) → ((p0 ∧ True) → False))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    intro assump_8
    have assump_21 : (p6 → True) := by
      intro assump_13
      apply True.intro
    let assump_12 := assump_5 assump_21
    apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p5 p3 p0 : Prop)
theorem file89_48370 : (((((False → False) ∧ (p3 ∨ p5)) → False) → (((p3 → False) ∨ (p0 ∨ p0)) ∨ ((False → False) → False))) ∨ ((((p5 → False) → (p0 → False)) → ((False → False) ∧ (p5 ∧ p3))) → (((p0 ∧ True) → False) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_15 : ((False → False) ∧ (p3 ∨ p5)) := by
    apply And.intro
    intro assump_9
    apply False.elim assump_9
    apply Or.inl
    exact assump_4
  let assump_8 := assump_1 assump_15
  apply False.elim assump_8


variable (p0 p7 p5 p1 p4 p3 p6 : Prop)
theorem file89_48948 : (((((True ∨ p6) → False) → ((p5 → p3) → (p3 → p7))) ∨ (((p3 ∧ p1) → (False ∨ True)) → ((p4 ∧ p0) ∧ (True → p5)))) ∨ ((((p4 → False) → False) ∨ ((False ∨ False) ∧ (p4 ∨ p7))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_14 : (True ∨ p6) := by
    apply Or.inl
    apply True.intro
  let assump_10 := assump_1 assump_14
  apply False.elim assump_10


variable (p0 p5 p6 p3 p1 p2 p7 p4 : Prop)
theorem file89_49427 : (((((p4 → False) → (p0 ∧ p2)) → ((p6 ∧ p2) → (True → False))) → (((p3 → p2) → (False → p6)) ∨ ((True → p5) → (False ∨ p1)))) ∨ ((((p5 → p3) ∨ (p7 ∧ p2)) → False) ∨ (((p5 ∧ p2) → (p4 ∨ p6)) → ((False → False) ∧ (p3 → p1))))) := by
  apply Or.inl
  intro assump_25
  apply Or.inl
  intro assump_28
  intro assump_29
  apply False.elim assump_29


variable (p6 p2 p5 p1 p3 : Prop)
theorem file89_49827 : ((((((p3 → p1) ∧ (p6 ∧ p2)) → ((False → p1) ∧ (p3 ∨ p2))) ∨ (((p5 → False) → False) ∧ ((p5 ∨ True) → (p6 ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p3 → p1) ∧ (p6 ∧ p2)) → ((False → p1) ∧ (p3 ∨ p2))) ∨ (((p5 → False) → False) ∧ ((p5 ∨ True) → (p6 ∧ p3)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    intro assump_6
    apply False.elim assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        apply Or.inr
        exact assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p3 p2 p6 p0 p7 p5 : Prop)
theorem file89_50512 : ((((((p6 → p0) ∧ (p2 → False)) → False) ∧ (((p7 → False) → (p3 ∨ p2)) → ((p7 → p6) → (False → p6)))) ∧ ((((False ∧ False) ∧ (False ∧ p5)) → ((p3 ∧ p3) ∧ (True → False))) ∧ (((p6 ∧ p5) → False) ∧ ((p2 → p2) → False)))) → False) := by
  intro assump_23
  cases assump_23
  case intro assump_24 assump_25 =>
    cases assump_24
    case intro assump_26 assump_27 =>
      cases assump_25
      case intro assump_32 assump_33 =>
        cases assump_33
        case intro assump_36 assump_37 =>
          have assump_49 : (p2 → p2) := by
            intro assump_43
            exact assump_43
          let assump_42 := assump_37 assump_49
          apply False.elim assump_42


variable (p7 p6 p3 p1 p2 p4 p5 p0 : Prop)
theorem file89_51252 : (((((p3 ∨ p3) ∧ (True ∨ p1)) ∨ ((p0 ∧ p1) ∧ (p3 → False))) ∨ (((True → False) ∧ (p4 ∧ p7)) → ((p6 ∧ p5) ∧ (p3 ∧ p2)))) ∨ ((((p2 → p7) ∨ (p4 → False)) → ((p7 → p6) → (p4 ∧ p6))) → (((p2 → False) → (p7 → False)) ∧ ((p7 → False) → False)))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_66 : True := by
        apply True.intro
      let assump_14 := assump_2 assump_66
      apply False.elim assump_14
  cases assump_1
  case intro assump_18 assump_19 =>
    cases assump_19
    case intro assump_22 assump_23 =>
      have assump_67 : True := by
        apply True.intro
      let assump_30 := assump_18 assump_67
      apply False.elim assump_30
  apply And.intro
  cases assump_1
  case intro assump_34 assump_35 =>
    cases assump_35
    case intro assump_38 assump_39 =>
      have assump_68 : True := by
        apply True.intro
      let assump_46 := assump_34 assump_68
      apply False.elim assump_46
  cases assump_1
  case intro assump_50 assump_51 =>
    cases assump_51
    case intro assump_54 assump_55 =>
      have assump_69 : True := by
        apply True.intro
      let assump_62 := assump_50 assump_69
      apply False.elim assump_62


variable (p1 p6 p4 p2 p0 p5 p3 p7 : Prop)
theorem file89_52641 : (((((p3 → True) ∨ (False → False)) ∨ ((p3 → p7) ∧ (False ∧ p0))) ∧ (((p6 ∨ p6) → (p0 ∨ p5)) → False)) → ((((p2 ∨ True) ∨ (p1 → p0)) ∨ ((p5 → p4) → (p3 → p6))) ∨ (((p1 ∨ p6) → False) ∧ ((True ∨ True) ∨ (True ∧ True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_7 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
    case inr assump_5 =>
      cases assump_5
      case intro assump_16 assump_17 =>
        cases assump_17
        case intro assump_20 assump_21 =>
          apply False.elim assump_20


variable (p3 p0 p2 p7 p1 p5 p4 : Prop)
theorem file89_53523 : (((((p7 ∧ p2) → False) → False) ∨ (((p7 ∧ True) ∧ (p3 ∧ p0)) ∧ ((p5 → False) → (p4 ∨ p2)))) → ((((p3 ∧ True) ∧ (p4 → p1)) → ((p4 → p7) → (p3 → True))) ∨ (((p7 → p0) ∧ (True → p5)) → ((p2 ∧ p0) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    intro assump_8
    apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_12
          case intro assump_19 assump_20 =>
            apply Or.inl
            intro assump_27
            intro assump_28
            intro assump_29
            apply True.intro


variable (p6 p2 p3 p5 p7 p1 p0 p4 : Prop)
theorem file89_54366 : (((((False ∨ p0) ∧ (p3 ∧ p5)) → ((p7 → p5) ∨ (p6 → p1))) ∨ (((p0 → False) → (p7 → False)) ∨ ((p2 ∧ p0) → False))) ∨ ((((p5 ∨ p6) ∨ (True ∧ p4)) → False) → (((p0 ∨ p2) → (p6 ∧ p3)) ∨ ((p1 ∧ p0) ∧ (True ∧ p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply False.elim assump_4
    case inr assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        apply Or.inl
        intro assump_16
        exact assump_11


variable (p4 p3 p7 p1 p5 : Prop)
theorem file89_54969 : (((((False → False) → False) → ((p3 → False) → False)) ∨ (((False ∨ p7) → False) → ((False ∧ p5) ∧ (p4 ∨ p1)))) ∨ ((((p7 → False) → False) ∨ ((False → p4) ∧ (True ∨ p4))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_14 : (False → False) := by
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7


variable (p7 p4 p2 p1 p0 p3 : Prop)
theorem file89_55435 : ((((((p3 ∧ p1) → False) ∨ ((False → False) ∨ (p7 → False))) → (((p2 ∧ p0) → (p0 → True)) ∧ ((p7 ∨ False) ∨ (p7 → p4)))) → False) → False) := by
  intro assump_5
  have assump_77 : ((((p3 ∧ p1) → False) ∨ ((False → False) ∨ (p7 → False))) → (((p2 ∧ p0) → (p0 → True)) ∧ ((p7 ∨ False) ∨ (p7 → p4)))) := by
    intro assump_9
    apply And.intro
    intro assump_10
    intro assump_11
    apply True.intro
    cases assump_9
    case inl assump_12 =>
      apply Or.inr
      intro assump_16
      have assump_78 : ((((p3 ∧ p1) → False) ∨ ((False → False) ∨ (p7 → False))) → (((p2 ∧ p0) → (p0 → True)) ∧ ((p7 ∨ False) ∨ (p7 → p4)))) := by
        intro assump_22
        apply And.intro
        intro assump_23
        intro assump_24
        apply True.intro
        cases assump_22
        case inl assump_25 =>
          apply Or.inl
          apply Or.inl
          exact assump_16
        case inr assump_26 =>
          cases assump_26
          case inl assump_29 =>
            apply Or.inl
            apply Or.inl
            exact assump_16
          case inr assump_30 =>
            apply Or.inl
            apply Or.inl
            exact assump_16
      let assump_21 := assump_5 assump_78
      apply False.elim assump_21
    case inr assump_13 =>
      cases assump_13
      case inl assump_38 =>
        apply Or.inr
        intro assump_42
        have assump_79 : ((((p3 ∧ p1) → False) ∨ ((False → False) ∨ (p7 → False))) → (((p2 ∧ p0) → (p0 → True)) ∧ ((p7 ∨ False) ∨ (p7 → p4)))) := by
          intro assump_48
          apply And.intro
          intro assump_49
          intro assump_50
          apply True.intro
          cases assump_48
          case inl assump_51 =>
            apply Or.inl
            apply Or.inl
            exact assump_42
          case inr assump_52 =>
            cases assump_52
            case inl assump_55 =>
              apply Or.inl
              apply Or.inl
              exact assump_42
            case inr assump_56 =>
              apply Or.inl
              apply Or.inl
              exact assump_42
        let assump_47 := assump_5 assump_79
        apply False.elim assump_47
      case inr assump_39 =>
        apply Or.inr
        intro assump_66
        have assump_80 : p7 := by
          exact assump_66
        let assump_70 := assump_39 assump_80
        apply False.elim assump_70
  let assump_8 := assump_5 assump_77
  apply False.elim assump_8


variable (p6 p0 p3 p5 p4 : Prop)
theorem file89_57917 : ((((((p3 ∨ p6) → False) → ((p5 ∨ True) ∨ (p5 → p5))) ∨ (((p4 ∨ p0) ∧ (p6 ∨ p4)) → ((p5 ∨ True) → (p3 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p3 ∨ p6) → False) → ((p5 ∨ True) ∨ (p5 → p5))) ∨ (((p4 ∨ p0) ∧ (p6 ∨ p4)) → ((p5 ∨ True) → (p3 ∧ p6)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p2 p5 p7 p4 p3 p1 : Prop)
theorem file89_58420 : (((((p4 ∧ p4) ∨ (p3 → False)) → False) → (((False ∨ p3) → False) ∨ ((p5 ∧ p2) ∨ (p6 ∧ False)))) → ((((p3 ∧ p6) → False) ∧ ((p2 ∧ p4) ∧ (p3 ∨ False))) → (((p5 → p1) ∨ (p7 ∧ p4)) → ((p6 → p4) ∨ (p7 ∧ p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_9
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_13
          case inl assump_20 =>
            apply Or.inl
            intro assump_26
            exact assump_15
          case inr assump_21 =>
            apply False.elim assump_21
  case inr assump_5 =>
    cases assump_5
    case intro assump_31 assump_32 =>
      cases assump_2
      case intro assump_37 assump_38 =>
        cases assump_38
        case intro assump_41 assump_42 =>
          cases assump_41
          case intro assump_43 assump_44 =>
            cases assump_42
            case inl assump_49 =>
              apply Or.inl
              intro assump_55
              exact assump_44
            case inr assump_50 =>
              apply False.elim assump_50


variable (p0 p7 p3 p4 : Prop)
theorem file89_59670 : ((((((p7 ∨ False) ∨ (False ∨ p0)) → ((True → p0) ∨ (p3 → False))) → False) ∧ ((((p4 → False) ∧ (False → False)) → ((p4 → False) → (p4 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_30 : (((p4 → False) ∧ (False → False)) → ((p4 → False) → (p4 → False))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      cases assump_9
      case intro assump_16 assump_17 =>
        have assump_31 : p4 := by
          exact assump_11
        let assump_23 := assump_16 assump_31
        apply False.elim assump_23
    let assump_8 := assump_3 assump_30
    apply False.elim assump_8


variable (p1 p4 p0 p6 p2 p5 p3 : Prop)
theorem file89_60400 : (((((p5 → False) → (True ∧ p5)) → ((p4 ∨ p0) → False)) → (((False ∧ p6) ∨ (False ∧ False)) → False)) ∨ ((((False ∨ p5) ∧ (p3 → p5)) → ((p6 ∨ p4) ∧ (p2 → False))) ∧ (((False → p2) → (p1 ∨ p5)) ∨ ((p4 → False) → (p6 ∧ p0))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5
  case inr assump_4 =>
    cases assump_4
    case intro assump_9 assump_10 =>
      apply False.elim assump_9


variable (p0 p3 p5 p6 p2 p4 : Prop)
theorem file89_60977 : ((((((p2 ∧ p4) → False) ∧ ((p0 → p2) ∨ (p4 → False))) → (((p5 → False) → (p3 ∨ p5)) ∧ ((p0 ∨ True) ∨ (p0 → p3)))) ∧ ((((False ∨ p2) ∧ (p6 → False)) ∨ ((p5 ∧ p0) ∧ (p3 → p2))) ∧ (((p6 → p2) → False) ∧ ((True ∨ p0) → False)))) → False) := by
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
            apply False.elim assump_12
          case inr assump_13 =>
            cases assump_7
            case intro assump_20 assump_21 =>
              have assump_50 : (True ∨ p0) := by
                apply Or.inl
                apply True.intro
              let assump_26 := assump_21 assump_50
              apply False.elim assump_26
      case inr assump_9 =>
        cases assump_9
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            cases assump_7
            case intro assump_40 assump_41 =>
              have assump_51 : (True ∨ p0) := by
                apply Or.inl
                apply True.intro
              let assump_46 := assump_41 assump_51
              apply False.elim assump_46


variable (p4 p2 p1 p7 p0 p6 p5 : Prop)
theorem file89_62359 : (((((p7 ∨ False) ∨ (p1 ∧ p6)) ∧ ((p5 → False) → (p6 → p0))) → False) → ((((p6 → p6) ∨ (p7 ∧ p0)) ∨ ((p4 → False) → False)) → (((p6 ∧ p2) → (p5 → True)) ∧ ((True ∧ p6) → (False → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  intro assump_4
  apply True.intro
  intro assump_5
  intro assump_6
  apply False.elim assump_6


variable (p1 p0 p2 p6 p4 p7 p5 : Prop)
theorem file89_62784 : ((((((p0 → False) → False) ∧ ((p7 → p0) ∧ (p6 ∧ p5))) → (((p6 ∨ p1) → False) ∧ ((p5 ∧ p4) → False))) ∧ ((((p2 ∧ p5) → (p6 ∨ True)) ∨ ((p1 ∨ p7) → (p5 ∧ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p2 ∧ p5) → (p6 ∨ True)) ∨ ((p1 ∨ p7) → (p5 ∧ p1))) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inr
        apply True.intro
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p0 p3 p7 p6 : Prop)
theorem file89_63386 : (((((p3 ∨ False) ∨ (p6 → p3)) → False) ∧ (((False ∧ p7) ∧ (True ∨ p7)) ∧ ((True ∨ p3) ∨ (p0 ∨ p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10


variable (p3 p2 p0 p1 p6 p5 : Prop)
theorem file89_63846 : (((((p1 ∨ p1) ∧ (p5 → False)) → False) ∧ (((p3 ∨ p2) → (p6 → p6)) → False)) → ((((p0 → False) ∧ (p5 → False)) ∧ ((False ∧ False) → (False → p6))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        have assump_33 : ((p3 ∨ p2) → (p6 → p6)) := by
          intro assump_20
          intro assump_21
          cases assump_20
          case inl assump_24 =>
            exact assump_21
          case inr assump_25 =>
            exact assump_21
        let assump_19 := assump_14 assump_33
        apply False.elim assump_19


variable (p2 p4 p6 : Prop)
theorem file89_64593 : (((((p4 → False) → False) → ((False ∧ False) → (p6 → p4))) → False) → ((((p2 ∧ p6) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_20 : (((p4 → False) → False) → ((False ∧ False) → (p6 → p4))) := by
    intro assump_8
    intro assump_9
    intro assump_10
    cases assump_9
    case intro assump_13 assump_14 =>
      apply False.elim assump_13
  let assump_7 := assump_1 assump_20
  apply False.elim assump_7


variable (p6 p4 p2 p5 p0 p1 : Prop)
theorem file89_65099 : (((((True ∧ p4) ∨ (p2 → p5)) → ((True ∨ p2) → False)) → (((p6 ∧ p1) → (p0 ∨ p1)) → ((p2 → p5) → (False → False)))) ∨ ((((p2 → False) ∨ (p0 ∧ False)) ∧ ((p6 → p1) → False)) ∧ (((False ∧ True) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply False.elim assump_4


variable (p3 p4 p2 p1 p0 p5 : Prop)
theorem file89_65487 : ((((((p4 ∧ False) ∧ (p3 → p2)) → ((p1 → False) ∨ (True ∨ p0))) ∨ (((p1 ∧ True) ∨ (p5 ∧ p0)) → False)) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p4 ∧ False) ∧ (p3 → p2)) → ((p1 → False) ∨ (True ∨ p0))) ∨ (((p1 ∧ True) ∨ (p5 ∧ p0)) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p7 p3 p4 p1 p0 p2 p6 : Prop)
theorem file89_66067 : (((((p4 ∨ p6) ∨ (p0 → False)) ∨ ((p1 → False) → False)) → False) → ((((p4 ∧ p7) ∨ (p4 ∧ p2)) ∧ ((p3 ∧ p1) ∨ (True ∨ p4))) → (((p3 ∧ p7) ∧ (False → True)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_2
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_15
            case inl assump_24 =>
              cases assump_24
              case intro assump_26 assump_27 =>
                have assump_94 : (((p4 ∨ p6) ∨ (p0 → False)) ∨ ((p1 → False) → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  exact assump_18
                let assump_34 := assump_1 assump_94
                apply False.elim assump_34
            case inr assump_25 =>
              cases assump_25
              case inl assump_38 =>
                have assump_95 : (((p4 ∨ p6) ∨ (p0 → False)) ∨ ((p1 → False) → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  exact assump_18
                let assump_44 := assump_1 assump_95
                apply False.elim assump_44
              case inr assump_39 =>
                have assump_96 : (((p4 ∨ p6) ∨ (p0 → False)) ∨ ((p1 → False) → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  exact assump_39
                let assump_52 := assump_1 assump_96
                apply False.elim assump_52
        case inr assump_17 =>
          cases assump_17
          case intro assump_56 assump_57 =>
            cases assump_15
            case inl assump_62 =>
              cases assump_62
              case intro assump_64 assump_65 =>
                have assump_97 : (((p4 ∨ p6) ∨ (p0 → False)) ∨ ((p1 → False) → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  exact assump_56
                let assump_72 := assump_1 assump_97
                apply False.elim assump_72
            case inr assump_63 =>
              cases assump_63
              case inl assump_76 =>
                have assump_98 : (((p4 ∨ p6) ∨ (p0 → False)) ∨ ((p1 → False) → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  exact assump_56
                let assump_82 := assump_1 assump_98
                apply False.elim assump_82
              case inr assump_77 =>
                have assump_99 : (((p4 ∨ p6) ∨ (p0 → False)) ∨ ((p1 → False) → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  exact assump_77
                let assump_90 := assump_1 assump_99
                apply False.elim assump_90


variable (p2 p6 p3 p0 p1 p4 p7 p5 : Prop)
theorem file89_69188 : ((((((p6 ∧ p0) → (p7 → p6)) ∨ ((p5 → False) → (p3 ∧ p4))) ∨ (((p1 ∧ True) ∨ (False ∨ p4)) ∨ ((p6 ∨ p2) ∨ (p7 → False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p6 ∧ p0) → (p7 → p6)) ∨ ((p5 → False) → (p3 ∧ p4))) ∨ (((p1 ∧ True) ∨ (False ∨ p4)) ∨ ((p6 ∨ p2) ∨ (p7 → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_9
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p6 p1 p5 p2 p4 p7 : Prop)
theorem file89_69771 : (((((p4 → p6) ∧ (p7 ∧ p6)) ∨ ((p1 ∧ True) → (p2 → False))) ∧ (((True → False) ∧ (p7 → False)) ∧ ((False ∧ p5) ∧ (p5 ∨ p4)))) → ((((p4 → False) → (p0 ∧ True)) ∧ ((True ∧ p7) → False)) → (((False → False) ∨ (p7 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case intro assump_8 assump_9 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_19
            case intro assump_22 assump_23 =>
              cases assump_15
              case intro assump_28 assump_29 =>
                cases assump_28
                case intro assump_30 assump_31 =>
                  cases assump_29
                  case intro assump_36 assump_37 =>
                    cases assump_36
                    case intro assump_38 assump_39 =>
                      apply False.elim assump_38
        case inr assump_17 =>
          cases assump_15
          case intro assump_44 assump_45 =>
            cases assump_44
            case intro assump_46 assump_47 =>
              cases assump_45
              case intro assump_52 assump_53 =>
                cases assump_52
                case intro assump_54 assump_55 =>
                  apply False.elim assump_54
  case inr assump_5 =>
    cases assump_2
    case intro assump_60 assump_61 =>
      cases assump_1
      case intro assump_66 assump_67 =>
        cases assump_66
        case inl assump_68 =>
          cases assump_68
          case intro assump_70 assump_71 =>
            cases assump_71
            case intro assump_74 assump_75 =>
              cases assump_67
              case intro assump_80 assump_81 =>
                cases assump_80
                case intro assump_82 assump_83 =>
                  cases assump_81
                  case intro assump_88 assump_89 =>
                    cases assump_88
                    case intro assump_90 assump_91 =>
                      apply False.elim assump_90
        case inr assump_69 =>
          cases assump_67
          case intro assump_96 assump_97 =>
            cases assump_96
            case intro assump_98 assump_99 =>
              cases assump_97
              case intro assump_104 assump_105 =>
                cases assump_104
                case intro assump_106 assump_107 =>
                  apply False.elim assump_106


variable (p1 p5 p2 p6 : Prop)
theorem file89_72339 : (((((p2 ∧ p6) ∧ (p5 ∨ p2)) → ((p2 → p1) → (p1 ∨ p6))) → False) → False) := by
  intro assump_1
  have assump_26 : (((p2 ∧ p6) ∧ (p5 ∨ p2)) → ((p2 → p1) → (p1 ∨ p6))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case inl assump_17 =>
          apply Or.inr
          exact assump_12
        case inr assump_18 =>
          apply Or.inr
          exact assump_12
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p6 p4 p3 p1 p5 : Prop)
theorem file89_72970 : ((((((p5 ∧ p3) ∨ (p1 ∨ p5)) ∧ ((False ∨ p3) → False)) → (((False → False) ∨ (p5 → False)) ∨ ((False ∧ p4) ∧ (p3 ∧ p6)))) → False) → False) := by
  intro assump_19
  have assump_58 : ((((p5 ∧ p3) ∨ (p1 ∨ p5)) ∧ ((False ∨ p3) → False)) → (((False → False) ∨ (p5 → False)) ∨ ((False ∧ p4) ∧ (p3 ∧ p6)))) := by
    intro assump_23
    cases assump_23
    case intro assump_24 assump_25 =>
      cases assump_24
      case inl assump_26 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          apply Or.inl
          apply Or.inl
          intro assump_36
          apply False.elim assump_36
      case inr assump_27 =>
        cases assump_27
        case inl assump_39 =>
          apply Or.inl
          apply Or.inl
          intro assump_45
          apply False.elim assump_45
        case inr assump_40 =>
          apply Or.inl
          apply Or.inl
          intro assump_52
          apply False.elim assump_52
  let assump_22 := assump_19 assump_58
  apply False.elim assump_22


variable (p0 p1 p6 p7 p5 p2 p3 p4 : Prop)
theorem file89_74044 : ((((((p1 ∧ False) ∧ (p0 → p6)) ∧ ((p2 → p6) → (p7 ∨ p3))) ∧ (((p5 → False) ∧ (p4 → p4)) ∧ ((p3 → False) ∧ (False → p6)))) ∧ ((((p1 → p4) → False) ∨ ((p5 → False) ∨ (p7 ∧ p2))) → (((p5 ∨ True) ∧ (p3 → False)) ∨ ((p3 ∨ p0) ∨ (p0 ∨ p4))))) → False) := by
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
            apply False.elim assump_11


variable (p2 p4 p1 p6 p3 p0 p7 p5 : Prop)
theorem file89_74715 : (((((False → False) ∧ (True ∨ p0)) → False) → (((p1 → False) → False) ∨ ((p7 ∨ False) → False))) ∨ ((((True ∨ p3) ∨ (True → p1)) ∨ ((True → False) → False)) ∧ (((p2 ∧ p6) ∨ (p4 ∧ p5)) ∧ ((True ∨ p3) ∨ (False → False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_15 : ((False → False) ∧ (True ∨ p0)) := by
    apply And.intro
    intro assump_9
    apply False.elim assump_9
    apply Or.inl
    apply True.intro
  let assump_8 := assump_1 assump_15
  apply False.elim assump_8


variable (p7 p6 p4 p2 : Prop)
theorem file89_75289 : (((((True ∨ True) → False) → False) → False) → ((((p4 ∨ True) ∧ (p6 ∨ p6)) → False) ∧ (((p2 → False) ∨ (p6 → False)) → ((p6 ∨ False) → (True ∨ p7))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case inl assump_9 =>
        have assump_93 : (((True ∨ True) → False) → False) := by
          intro assump_16
          have assump_94 : (True ∨ True) := by
            apply Or.inl
            apply True.intro
          let assump_19 := assump_16 assump_94
          apply False.elim assump_19
        let assump_15 := assump_1 assump_93
        apply False.elim assump_15
      case inr assump_10 =>
        have assump_95 : (((True ∨ True) → False) → False) := by
          intro assump_31
          have assump_96 : (True ∨ True) := by
            apply Or.inl
            apply True.intro
          let assump_34 := assump_31 assump_96
          apply False.elim assump_34
        let assump_30 := assump_1 assump_95
        apply False.elim assump_30
    case inr assump_6 =>
      cases assump_4
      case inl assump_43 =>
        have assump_97 : (((True ∨ True) → False) → False) := by
          intro assump_50
          have assump_98 : (True ∨ True) := by
            apply Or.inl
            apply True.intro
          let assump_53 := assump_50 assump_98
          apply False.elim assump_53
        let assump_49 := assump_1 assump_97
        apply False.elim assump_49
      case inr assump_44 =>
        have assump_99 : (((True ∨ True) → False) → False) := by
          intro assump_65
          have assump_100 : (True ∨ True) := by
            apply Or.inl
            apply True.intro
          let assump_68 := assump_65 assump_100
          apply False.elim assump_68
        let assump_64 := assump_1 assump_99
        apply False.elim assump_64
  intro assump_75
  intro assump_76
  cases assump_76
  case inl assump_77 =>
    cases assump_75
    case inl assump_81 =>
      apply Or.inl
      apply True.intro
    case inr assump_82 =>
      apply Or.inl
      apply True.intro
  case inr assump_78 =>
    apply False.elim assump_78


variable (p5 p4 p7 p2 p1 : Prop)
theorem file89_77539 : ((((((p4 ∧ p1) ∨ (p7 ∨ p5)) ∨ ((True → p5) → (p2 → p2))) ∧ (((p7 ∨ p2) → False) → ((p7 → False) ∨ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p4 ∧ p1) ∨ (p7 ∨ p5)) ∨ ((True → p5) → (p2 → p2))) ∧ (((p7 ∨ p2) → False) → ((p7 → False) ∨ (False → False)))) := by
    apply And.intro
    apply Or.inr
    intro assump_5
    intro assump_6
    exact assump_6
    intro assump_11
    apply Or.inl
    intro assump_14
    have assump_26 : (p7 ∨ p2) := by
      apply Or.inl
      exact assump_14
    let assump_18 := assump_11 assump_26
    apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p6 p5 p7 : Prop)
theorem file89_78254 : (((((p6 ∧ p5) ∧ (p7 → False)) → ((True → False) → False)) → False) → False) := by
  intro assump_1
  have assump_29 : (((p6 ∧ p5) ∧ (p7 → False)) → ((True → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        have assump_30 : True := by
          apply True.intro
        let assump_22 := assump_6 assump_30
        apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p2 p5 p6 p7 p0 : Prop)
theorem file89_78853 : ((((((p6 → p6) ∧ (p5 ∧ p7)) ∧ ((p0 → False) ∨ (True ∨ p6))) → (((p2 → False) → (True → True)) ∨ ((p5 → p7) → (True → p5)))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((p6 → p6) ∧ (p5 ∧ p7)) ∧ ((p0 → False) ∨ (True ∨ p6))) → (((p2 → False) → (True → True)) ∨ ((p5 → p7) → (True → p5)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_7
          case inl assump_18 =>
            apply Or.inl
            intro assump_22
            intro assump_23
            apply True.intro
          case inr assump_19 =>
            cases assump_19
            case inl assump_24 =>
              apply Or.inl
              intro assump_28
              intro assump_29
              apply True.intro
            case inr assump_25 =>
              apply Or.inl
              intro assump_32
              intro assump_33
              apply True.intro
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p1 p0 p3 p2 p5 p7 : Prop)
theorem file89_80019 : (((((p3 ∧ p1) → False) → False) ∧ (((False ∧ p3) ∧ (False → p0)) ∧ ((p2 ∧ p5) ∨ (p7 ∧ p7)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10


variable (p1 p7 p3 p4 : Prop)
theorem file89_80465 : (((((p7 ∧ False) → (False → p1)) ∧ ((p3 → False) → (p3 → p4))) → False) → False) := by
  intro assump_1
  have assump_22 : (((p7 ∧ False) → (False → p1)) ∧ ((p3 → False) → (p3 → p4))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    apply False.elim assump_6
    intro assump_9
    intro assump_10
    have assump_23 : p3 := by
      exact assump_10
    let assump_15 := assump_9 assump_23
    apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p7 p3 p1 p6 p0 : Prop)
theorem file89_81027 : ((((((p7 ∧ p0) ∨ (True → p6)) → False) → False) ∧ ((((p1 ∧ False) → (p0 ∨ p1)) ∨ ((p3 ∨ p0) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p1 ∧ False) → (p0 ∨ p1)) ∨ ((p3 ∨ p0) → False)) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p4 p5 p0 p7 p6 p2 p3 : Prop)
theorem file89_81568 : (((((p7 ∨ True) → False) → ((p0 ∨ p2) → False)) → (((p2 → False) ∨ (p7 → False)) → ((p7 ∧ p4) → (p7 ∧ True)))) ∨ ((((p6 → True) ∧ (p3 → p0)) → ((p4 ∧ p3) → False)) ∧ (((p5 → p6) ∧ (False → p4)) ∨ ((p2 → True) ∨ (p3 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case inl assump_10 =>
      exact assump_4
    case inr assump_11 =>
      exact assump_4
  apply True.intro


variable (p1 p6 p5 p3 p4 p7 p2 : Prop)
theorem file89_82132 : ((((((p5 ∧ p4) → (p1 ∨ p4)) ∧ ((p4 → False) → (p7 ∨ p6))) ∨ (((p3 → p6) → False) → ((p7 → False) ∨ (p6 → p3)))) ∧ ((((p7 → True) → False) → ((p2 → False) ∧ (p2 → p2))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        have assump_62 : (((p7 → True) → False) → ((p2 → False) ∧ (p2 → p2))) := by
          intro assump_19
          apply And.intro
          intro assump_20
          have assump_63 : (p7 → True) := by
            intro assump_26
            apply True.intro
          let assump_25 := assump_19 assump_63
          apply False.elim assump_25
          intro assump_30
          exact assump_30
        let assump_18 := assump_7 assump_62
        apply False.elim assump_18
    case inr assump_9 =>
      have assump_64 : (((p7 → True) → False) → ((p2 → False) ∧ (p2 → p2))) := by
        intro assump_43
        apply And.intro
        intro assump_44
        have assump_65 : (p7 → True) := by
          intro assump_50
          apply True.intro
        let assump_49 := assump_43 assump_65
        apply False.elim assump_49
        intro assump_54
        exact assump_54
      let assump_42 := assump_7 assump_64
      apply False.elim assump_42


variable (p3 p5 p7 : Prop)
theorem file89_83506 : ((((((p3 → p3) → (p5 → True)) → False) → (((p5 → False) ∨ (p3 → p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p3 → p3) → (p5 → True)) → False) → (((p5 → False) ∨ (p3 → p7)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_33 : ((p3 → p3) → (p5 → True)) := by
        intro assump_14
        intro assump_15
        apply True.intro
      let assump_13 := assump_5 assump_33
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_34 : ((p3 → p3) → (p5 → True)) := by
        intro assump_24
        intro assump_25
        apply True.intro
      let assump_23 := assump_5 assump_34
      apply False.elim assump_23
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p4 p5 p1 : Prop)
theorem file89_84357 : ((((((False ∨ False) → False) → ((p4 → True) → False)) → (((p5 ∧ p5) ∨ (p5 → False)) → ((p1 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_53 : ((((False ∨ False) → False) → ((p4 → True) → False)) → (((p5 ∧ p5) ∨ (p5 → False)) → ((p1 → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        have assump_54 : ((False ∨ False) → False) := by
          intro assump_21
          cases assump_21
          case inl assump_22 =>
            apply False.elim assump_22
          case inr assump_23 =>
            apply False.elim assump_23
        let assump_20 := assump_5 assump_54
        have assump_55 : (p4 → True) := by
          intro assump_29
          apply True.intro
        let assump_28 := assump_20 assump_55
        apply False.elim assump_28
    case inr assump_11 =>
      have assump_56 : ((False ∨ False) → False) := by
        intro assump_38
        cases assump_38
        case inl assump_39 =>
          apply False.elim assump_39
        case inr assump_40 =>
          apply False.elim assump_40
      let assump_37 := assump_5 assump_56
      have assump_57 : (p4 → True) := by
        intro assump_46
        apply True.intro
      let assump_45 := assump_37 assump_57
      apply False.elim assump_45
  let assump_4 := assump_1 assump_53
  apply False.elim assump_4


variable (p5 p3 p0 p4 p1 : Prop)
theorem file89_85873 : (((((p0 ∧ False) → False) → False) → (((p3 → False) ∨ (p1 ∧ p3)) ∨ ((p4 → p4) → False))) ∨ ((((p5 ∨ True) → (p0 → p4)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_19 : ((p0 ∧ False) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_11
  let assump_8 := assump_1 assump_19
  apply False.elim assump_8


variable (p5 p3 p0 p7 p6 p1 : Prop)
theorem file89_86378 : (((((p0 → False) ∧ (p7 ∨ False)) → ((True → False) → (p0 ∧ True))) → False) → ((((False → False) ∨ (True ∧ True)) → False) → (((p5 ∧ p0) ∧ (True ∧ p6)) → ((p3 → False) ∨ (p1 ∨ p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_5
      case intro assump_12 assump_13 =>
        apply Or.inl
        intro assump_22
        have assump_44 : (((p0 → False) ∧ (p7 ∨ False)) → ((True → False) → (p0 ∧ True))) := by
          intro assump_27
          intro assump_28
          apply And.intro
          cases assump_27
          case intro assump_31 assump_32 =>
            cases assump_32
            case inl assump_35 =>
              exact assump_7
            case inr assump_36 =>
              apply False.elim assump_36
          apply True.intro
        let assump_26 := assump_1 assump_44
        apply False.elim assump_26


variable (p5 p7 p4 p3 p2 : Prop)
theorem file89_87404 : (((((True ∧ p3) ∧ (p5 ∨ p4)) ∨ ((p7 ∨ p2) → (p3 ∨ p3))) → (((False → False) → False) → False)) ∨ ((((p5 ∨ p3) → (True → False)) → ((p4 → False) → False)) → (((True → True) → (p2 → p7)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case inl assump_15 =>
          have assump_49 : (False → False) := by
            intro assump_22
            apply False.elim assump_22
          let assump_21 := assump_2 assump_49
          apply False.elim assump_21
        case inr assump_16 =>
          have assump_50 : (False → False) := by
            intro assump_33
            apply False.elim assump_33
          let assump_32 := assump_2 assump_50
          apply False.elim assump_32
  case inr assump_6 =>
    have assump_51 : (False → False) := by
      intro assump_43
      apply False.elim assump_43
    let assump_42 := assump_2 assump_51
    apply False.elim assump_42


variable (p0 p3 p2 p1 : Prop)
theorem file89_88537 : ((((((p3 → p0) ∧ (True → False)) ∧ ((p0 → False) ∨ (p2 ∨ True))) → (((p1 → False) → (False → True)) ∧ ((p1 ∧ p0) → (p3 → p2)))) → False) → False) := by
  intro assump_1
  have assump_47 : ((((p3 → p0) ∧ (True → False)) ∧ ((p0 → False) ∨ (p2 ∨ True))) → (((p1 → False) → (False → True)) ∧ ((p1 ∧ p0) → (p3 → p2)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    apply True.intro
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      cases assump_5
      case intro assump_18 assump_19 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          cases assump_19
          case inl assump_26 =>
            have assump_48 : p0 := by
              exact assump_13
            let assump_30 := assump_26 assump_48
            apply False.elim assump_30
          case inr assump_27 =>
            cases assump_27
            case inl assump_34 =>
              exact assump_34
            case inr assump_35 =>
              have assump_49 : True := by
                apply True.intro
              let assump_40 := assump_21 assump_49
              apply False.elim assump_40
  let assump_4 := assump_1 assump_47
  apply False.elim assump_4


variable (p5 : Prop)
theorem file89_89826 : ((((((False ∧ p5) → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False ∧ p5) → False) → False) → False) := by
    intro assump_5
    have assump_21 : ((False ∧ p5) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_5 assump_21
    apply False.elim assump_8
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p0 p5 p3 p2 p4 p7 : Prop)
theorem file89_90360 : (((((p4 ∧ p2) → False) → ((p0 → False) ∧ (p5 → p0))) → (((p5 ∨ p7) ∨ (False → False)) ∧ ((False → False) ∨ (False ∧ False)))) ∨ ((((True → p3) → (p5 → False)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply Or.inr
  intro assump_4
  apply False.elim assump_4
  apply Or.inl
  intro assump_9
  apply False.elim assump_9


variable (p1 p7 p4 p2 p5 p0 p6 : Prop)
theorem file89_90777 : (((((p4 → True) ∨ (p7 → p6)) ∧ ((p4 → p1) → (False → False))) ∨ (((True → False) ∧ (p1 → False)) ∧ ((False → False) ∧ (p1 → False)))) → ((((p5 ∨ p2) ∧ (p4 ∧ p1)) → ((False ∧ p2) → (p0 ∧ False))) ∨ (((p4 ∧ p2) → (p6 ∨ p7)) ∨ ((p0 → p6) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        intro assump_12
        intro assump_13
        apply And.intro
        cases assump_13
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
        cases assump_13
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
      case inr assump_7 =>
        apply Or.inl
        intro assump_26
        intro assump_27
        apply And.intro
        cases assump_27
        case intro assump_28 assump_29 =>
          apply False.elim assump_28
        cases assump_27
        case intro assump_32 assump_33 =>
          apply False.elim assump_32
  case inr assump_3 =>
    cases assump_3
    case intro assump_36 assump_37 =>
      cases assump_36
      case intro assump_38 assump_39 =>
        cases assump_37
        case intro assump_44 assump_45 =>
          apply Or.inl
          intro assump_50
          intro assump_51
          apply And.intro
          cases assump_51
          case intro assump_52 assump_53 =>
            apply False.elim assump_52
          cases assump_51
          case intro assump_56 assump_57 =>
            apply False.elim assump_56


variable (p6 p3 p5 p1 p7 p0 p4 p2 : Prop)
theorem file89_92408 : ((((((False ∧ True) ∨ (p7 ∧ p6)) → ((p5 ∧ p3) ∨ (p0 ∨ p7))) → (((p4 → p6) ∧ (p6 ∨ p1)) → ((p1 → p3) ∧ (p5 → p4)))) ∧ ((((p3 ∧ p2) → (p2 → False)) → ((True → p0) → (p3 → p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_21 : (((p3 ∧ p2) → (p2 → False)) → ((True → p0) → (p3 → p3))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      exact assump_11
    let assump_8 := assump_3 assump_21
    apply False.elim assump_8


variable (p1 p3 p5 p4 p7 p2 : Prop)
theorem file89_92976 : (((((p4 ∨ p5) → (p5 → False)) → ((False ∨ p2) ∨ (p2 → False))) → False) → ((((p2 ∨ p3) ∧ (p4 ∨ p5)) ∨ ((True → p5) ∨ (p4 → True))) ∧ (((p2 ∨ p5) ∨ (p7 → False)) → ((p2 → False) ∧ (p1 → p4))))) := by
  intro assump_1
  apply And.intro
  apply Or.inr
  apply Or.inl
  intro assump_4
  have assump_128 : (((p4 ∨ p5) → (p5 → False)) → ((False ∨ p2) ∨ (p2 → False))) := by
    intro assump_8
    apply Or.inr
    intro assump_11
    have assump_129 : (((p4 ∨ p5) → (p5 → False)) → ((False ∨ p2) ∨ (p2 → False))) := by
      intro assump_17
      apply Or.inl
      apply Or.inr
      exact assump_11
    let assump_16 := assump_1 assump_129
    apply False.elim assump_16
  let assump_7 := assump_1 assump_128
  apply False.elim assump_7
  intro assump_26
  apply And.intro
  intro assump_27
  cases assump_26
  case inl assump_30 =>
    cases assump_30
    case inl assump_32 =>
      have assump_130 : (((p4 ∨ p5) → (p5 → False)) → ((False ∨ p2) ∨ (p2 → False))) := by
        intro assump_39
        apply Or.inl
        apply Or.inr
        exact assump_32
      let assump_38 := assump_1 assump_130
      apply False.elim assump_38
    case inr assump_33 =>
      have assump_131 : (((p4 ∨ p5) → (p5 → False)) → ((False ∨ p2) ∨ (p2 → False))) := by
        intro assump_50
        apply Or.inl
        apply Or.inr
        exact assump_27
      let assump_49 := assump_1 assump_131
      apply False.elim assump_49
  case inr assump_31 =>
    have assump_132 : (((p4 ∨ p5) → (p5 → False)) → ((False ∨ p2) ∨ (p2 → False))) := by
      intro assump_61
      apply Or.inl
      apply Or.inr
      exact assump_27
    let assump_60 := assump_1 assump_132
    apply False.elim assump_60
  intro assump_67
  cases assump_26
  case inl assump_70 =>
    cases assump_70
    case inl assump_72 =>
      have assump_133 : (((p4 ∨ p5) → (p5 → False)) → ((False ∨ p2) ∨ (p2 → False))) := by
        intro assump_79
        apply Or.inl
        apply Or.inr
        exact assump_72
      let assump_78 := assump_1 assump_133
      apply False.elim assump_78
    case inr assump_73 =>
      have assump_134 : (((p4 ∨ p5) → (p5 → False)) → ((False ∨ p2) ∨ (p2 → False))) := by
        intro assump_90
        apply Or.inr
        intro assump_93
        have assump_135 : (p4 ∨ p5) := by
          apply Or.inr
          exact assump_73
        let assump_97 := assump_90 assump_135
        have assump_136 : p5 := by
          exact assump_73
        let assump_98 := assump_97 assump_136
        apply False.elim assump_98
      let assump_89 := assump_1 assump_134
      apply False.elim assump_89
  case inr assump_71 =>
    have assump_137 : (((p4 ∨ p5) → (p5 → False)) → ((False ∨ p2) ∨ (p2 → False))) := by
      intro assump_110
      apply Or.inr
      intro assump_113
      have assump_138 : (((p4 ∨ p5) → (p5 → False)) → ((False ∨ p2) ∨ (p2 → False))) := by
        intro assump_119
        apply Or.inl
        apply Or.inr
        exact assump_113
      let assump_118 := assump_1 assump_138
      apply False.elim assump_118
    let assump_109 := assump_1 assump_137
    apply False.elim assump_109


