variable (p3 p4 p7 p0 p6 p1 p5 : Prop)
theorem file47_47 : (((((p0 ∨ True) → (p5 → p7)) → ((False ∧ True) → False)) → False) → ((((p5 ∧ p7) → False) ∨ ((p3 → False) ∧ (p6 → False))) ∨ (((p4 → False) ∧ (p1 → p6)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_23 : (((p0 ∨ True) → (p5 → p7)) → ((False ∧ True) → False)) := by
      intro assump_14
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        apply False.elim assump_16
    let assump_13 := assump_1 assump_23
    apply False.elim assump_13


variable (p5 p3 p4 p0 p2 p1 : Prop)
theorem file47_686 : (((((True ∧ p0) ∨ (False → False)) → False) → (((p2 ∨ p3) → (p5 ∨ p5)) ∧ ((p0 → False) ∨ (p2 ∨ p2)))) ∨ ((((p5 → False) → (p0 ∧ p4)) → False) ∧ (((p3 → False) ∨ (p2 → p1)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_37 : ((True ∧ p0) ∨ (False → False)) := by
      apply Or.inr
      intro assump_10
      apply False.elim assump_10
    let assump_9 := assump_1 assump_37
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_38 : ((True ∧ p0) ∨ (False → False)) := by
      apply Or.inr
      intro assump_21
      apply False.elim assump_21
    let assump_20 := assump_1 assump_38
    apply False.elim assump_20
  apply Or.inl
  intro assump_29
  have assump_39 : ((True ∧ p0) ∨ (False → False)) := by
    apply Or.inl
    apply And.intro
    apply True.intro
    exact assump_29
  let assump_33 := assump_1 assump_39
  apply False.elim assump_33


variable (p1 p3 p4 p7 p5 p2 : Prop)
theorem file47_1706 : (((((False → False) → False) ∧ ((p1 ∧ p5) ∧ (p2 → False))) → False) ∨ ((((p7 → False) ∨ (p3 → False)) → ((p5 → p4) ∧ (p5 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_26 : (False → False) := by
          intro assump_20
          apply False.elim assump_20
        let assump_19 := assump_2 assump_26
        apply False.elim assump_19


variable (p3 p6 p4 p7 p5 p0 p2 p1 : Prop)
theorem file47_2306 : (((((p2 ∨ p1) → (p1 ∧ p3)) ∧ ((p4 → False) → False)) ∧ (((p6 ∨ False) → (False ∨ p5)) → ((p3 → p1) → (p7 ∧ p3)))) → ((((True ∧ p1) ∧ (p7 ∧ p5)) ∨ ((False ∧ p6) → False)) → (((p5 ∧ False) → (p1 ∨ p6)) ∧ ((p0 ∨ True) ∨ (p5 ∧ p0))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_5
  cases assump_2
  case inl assump_10 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_13
        case intro assump_20 assump_21 =>
          cases assump_1
          case intro assump_26 assump_27 =>
            cases assump_26
            case intro assump_28 assump_29 =>
              apply Or.inl
              apply Or.inr
              apply True.intro
  case inr assump_11 =>
    cases assump_1
    case intro assump_38 assump_39 =>
      cases assump_38
      case intro assump_40 assump_41 =>
        apply Or.inl
        apply Or.inr
        apply True.intro


variable (p5 p2 p6 : Prop)
theorem file47_3409 : (((((p2 ∨ p6) ∧ (False ∧ p5)) → False) → False) → False) := by
  intro assump_4
  have assump_28 : (((p2 ∨ p6) ∧ (False ∧ p5)) → False) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          apply False.elim assump_15
      case inr assump_12 =>
        cases assump_10
        case intro assump_21 assump_22 =>
          apply False.elim assump_21
  let assump_7 := assump_4 assump_28
  apply False.elim assump_7


variable (p2 p0 p1 p5 p3 p4 p6 : Prop)
theorem file47_4037 : (((((p2 ∨ p1) ∨ (False → False)) ∨ ((True → p1) ∧ (p2 ∨ p1))) → False) → ((((p1 → False) ∨ (p0 → p1)) ∨ ((p6 ∧ p4) → (p1 ∨ True))) ∨ (((p5 → p3) ∧ (p1 ∧ p1)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_12 : (((p2 ∨ p1) ∨ (False → False)) ∨ ((True → p1) ∧ (p2 ∨ p1))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    exact assump_4
  let assump_8 := assump_1 assump_12
  apply False.elim assump_8


variable (p6 p4 p7 p5 p1 p3 p0 p2 : Prop)
theorem file47_4577 : (((((p1 ∨ p0) ∨ (p7 → True)) ∨ ((p6 ∨ p5) → False)) ∨ (((p1 ∧ p3) ∧ (p6 → p7)) ∧ ((p5 ∧ p4) → False))) ∨ ((((False → p3) → (p6 → p2)) ∨ ((True → False) → False)) ∨ (((p5 → False) ∨ (p2 → p5)) → ((p1 → False) ∧ (p3 → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply True.intro


variable (p0 p1 : Prop)
theorem file47_4954 : ((((((p1 ∨ False) → (p0 → p1)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p1 ∨ False) → (p0 → p1)) → False) → False) := by
    intro assump_5
    have assump_26 : ((p1 ∨ False) → (p0 → p1)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case inl assump_13 =>
        exact assump_13
      case inr assump_14 =>
        apply False.elim assump_14
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p1 p0 p5 p2 p4 p7 p6 : Prop)
theorem file47_5565 : ((((((p4 ∧ p7) ∧ (p4 ∧ p1)) ∧ ((p7 ∧ p0) → (p2 → False))) ∧ (((True → False) ∨ (p6 ∨ False)) ∧ ((False → False) ∧ (p1 → True)))) ∧ ((((p7 ∨ p2) → (p5 → False)) → ((p5 → False) ∧ (True ∧ p7))) → (((p5 ∨ p4) ∧ (False → False)) → False))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              cases assump_9
              case intro assump_28 assump_29 =>
                cases assump_28
                case inl assump_30 =>
                  cases assump_29
                  case intro assump_34 assump_35 =>
                    have assump_98 : (((p7 ∨ p2) → (p5 → False)) → ((p5 → False) ∧ (True ∧ p7))) := by
                      intro assump_43
                      apply And.intro
                      intro assump_44
                      have assump_99 : (p7 ∨ p2) := by
                        apply Or.inl
                        exact assump_15
                      let assump_49 := assump_43 assump_99
                      have assump_100 : p5 := by
                        exact assump_44
                      let assump_50 := assump_49 assump_100
                      apply False.elim assump_50
                      apply And.intro
                      apply True.intro
                      exact assump_15
                    let assump_42 := assump_7 assump_98
                    have assump_101 : ((p5 ∨ p4) ∧ (False → False)) := by
                      apply And.intro
                      apply Or.inr
                      exact assump_20
                      intro assump_57
                      apply False.elim assump_57
                    let assump_56 := assump_42 assump_101
                    apply False.elim assump_56
                case inr assump_31 =>
                  cases assump_31
                  case inl assump_63 =>
                    cases assump_29
                    case intro assump_67 assump_68 =>
                      have assump_102 : (((p7 ∨ p2) → (p5 → False)) → ((p5 → False) ∧ (True ∧ p7))) := by
                        intro assump_76
                        apply And.intro
                        intro assump_77
                        have assump_103 : (p7 ∨ p2) := by
                          apply Or.inl
                          exact assump_15
                        let assump_82 := assump_76 assump_103
                        have assump_104 : p5 := by
                          exact assump_77
                        let assump_83 := assump_82 assump_104
                        apply False.elim assump_83
                        apply And.intro
                        apply True.intro
                        exact assump_15
                      let assump_75 := assump_7 assump_102
                      have assump_105 : ((p5 ∨ p4) ∧ (False → False)) := by
                        apply And.intro
                        apply Or.inr
                        exact assump_20
                        intro assump_90
                        apply False.elim assump_90
                      let assump_89 := assump_75 assump_105
                      apply False.elim assump_89
                  case inr assump_64 =>
                    apply False.elim assump_64


variable (p7 p4 p2 p1 p3 p6 p5 : Prop)
theorem file47_9155 : (((((False → False) ∨ (p3 → p4)) ∨ ((p6 → True) → False)) → False) → ((((p3 ∧ False) ∨ (p7 → False)) ∧ ((p4 → p3) ∧ (p1 ∧ p7))) → (((p5 → p4) → False) → ((p7 ∧ p2) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_2
    case intro assump_13 assump_14 =>
      cases assump_13
      case inl assump_15 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          apply False.elim assump_18
      case inr assump_16 =>
        cases assump_14
        case intro assump_25 assump_26 =>
          cases assump_26
          case intro assump_29 assump_30 =>
            have assump_44 : (((False → False) ∨ (p3 → p4)) ∨ ((p6 → True) → False)) := by
              apply Or.inl
              apply Or.inl
              intro assump_38
              apply False.elim assump_38
            let assump_37 := assump_1 assump_44
            apply False.elim assump_37


variable (p7 p0 p2 p1 p5 p3 : Prop)
theorem file47_10193 : (((((True ∨ p5) → (p7 ∧ p5)) → ((p3 → True) ∧ (p1 ∨ p3))) → (((p5 ∧ True) ∨ (False ∧ p0)) ∨ ((False → False) ∨ (False → p2)))) ∨ ((((False → False) → False) → False) ∧ (((p3 ∧ p2) → False) ∧ ((p0 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p3 p7 p1 : Prop)
theorem file47_10574 : (((((False ∧ p3) → (p3 → p1)) ∨ ((p7 → False) → False)) → False) → False) := by
  intro assump_15
  have assump_30 : (((False ∧ p3) → (p3 → p1)) ∨ ((p7 → False) → False)) := by
    apply Or.inl
    intro assump_19
    intro assump_20
    cases assump_19
    case intro assump_23 assump_24 =>
      apply False.elim assump_23
  let assump_18 := assump_15 assump_30
  apply False.elim assump_18


variable (p1 p2 p6 p5 p7 : Prop)
theorem file47_11024 : ((((((p2 → p6) ∨ (p7 ∨ p6)) → False) → (((False ∨ p2) → (p1 ∧ p2)) → ((p5 ∨ p5) ∨ (False → True)))) → ((((True ∨ p2) → False) → ((p7 ∨ p7) ∧ (True → False))) → False)) → False) := by
  intro assump_1
  have assump_32 : ((((p2 → p6) ∨ (p7 ∨ p6)) → False) → (((False ∨ p2) → (p1 ∧ p2)) → ((p5 ∨ p5) ∨ (False → True)))) := by
    intro assump_5
    intro assump_6
    apply Or.inr
    intro assump_11
    apply True.intro
  let assump_4 := assump_1 assump_32
  have assump_33 : (((True ∨ p2) → False) → ((p7 ∨ p7) ∧ (True → False))) := by
    intro assump_13
    apply And.intro
    have assump_34 : (True ∨ p2) := by
      apply Or.inl
      apply True.intro
    let assump_16 := assump_13 assump_34
    apply False.elim assump_16
    intro assump_20
    have assump_35 : (True ∨ p2) := by
      apply Or.inl
      apply True.intro
    let assump_25 := assump_13 assump_35
    apply False.elim assump_25
  let assump_12 := assump_4 assump_33
  apply False.elim assump_12


variable (p1 p4 p0 p2 p6 p5 : Prop)
theorem file47_12053 : (((((p1 → False) ∧ (p5 ∧ p5)) ∧ ((False ∧ p1) ∧ (p5 → p0))) → (((p4 → True) ∨ (p6 ∨ p6)) ∨ ((p2 → False) ∧ (p6 ∧ p4)))) ∨ ((((p5 → p1) ∧ (p5 ∨ False)) ∧ ((p2 → True) ∨ (p1 ∨ p2))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            apply False.elim assump_16


variable (p7 p5 : Prop)
theorem file47_12668 : ((((((False → False) → False) ∧ ((p7 → True) → (p5 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((False → False) → False) ∧ ((p7 → True) → (p5 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_26 : (False → False) := by
        intro assump_16
        apply False.elim assump_16
      let assump_15 := assump_6 assump_26
      apply False.elim assump_15
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p6 p2 p5 p7 p4 p0 p1 p3 : Prop)
theorem file47_13258 : (((((p6 ∨ p3) ∧ (p0 → p0)) → False) ∧ (((p1 → False) → (p1 ∨ False)) ∧ ((p0 → p5) → (p1 ∨ p3)))) → ((((False ∧ p4) ∨ (p2 → p5)) ∧ ((p4 → True) → (p7 → False))) → (((False ∨ False) → (p2 → False)) ∨ ((p4 → False) → (p5 ∨ True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7
    case inr assump_6 =>
      cases assump_1
      case intro assump_15 assump_16 =>
        cases assump_16
        case intro assump_19 assump_20 =>
          apply Or.inl
          intro assump_25
          intro assump_26
          cases assump_25
          case inl assump_29 =>
            apply False.elim assump_29
          case inr assump_30 =>
            apply False.elim assump_30


variable (p0 p1 p5 p6 p7 p2 p3 p4 : Prop)
theorem file47_14177 : (((((p3 ∨ p2) ∧ (p6 → p0)) → ((p2 → False) → (True ∧ p3))) ∨ (((p0 → False) ∨ (p5 ∨ p1)) ∨ ((p3 ∧ p1) ∨ (p4 → False)))) ∨ ((((False ∧ p7) → (p7 ∧ False)) → False) ∨ (((p3 ∧ p3) → False) → ((p0 → p0) ∧ (p5 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  apply True.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      exact assump_7
    case inr assump_8 =>
      have assump_23 : p2 := by
        exact assump_8
      let assump_19 := assump_2 assump_23
      apply False.elim assump_19


variable (p2 p7 p5 p3 p6 p4 p1 : Prop)
theorem file47_14836 : (((((True ∧ True) ∧ (p1 → p6)) → False) → (((p2 → False) ∨ (p1 ∧ p4)) ∨ ((p6 → p2) → (p4 → False)))) → ((((p5 ∨ True) → (p3 ∧ p2)) → False) → (((p4 → p6) → (p1 ∧ False)) → ((True → p7) → (p3 → True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply True.intro


variable (p4 p7 p3 p0 p6 p5 : Prop)
theorem file47_15209 : (((((p6 ∨ p6) ∧ (p7 ∧ p0)) → ((True → False) → False)) ∨ (((p0 ∧ p4) ∨ (p0 → p5)) ∨ ((p5 ∧ p5) → False))) ∨ ((((p7 ∨ p3) → False) ∨ ((False → False) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        have assump_39 : True := by
          apply True.intro
        let assump_20 := assump_2 assump_39
        apply False.elim assump_20
    case inr assump_8 =>
      cases assump_6
      case intro assump_26 assump_27 =>
        have assump_40 : True := by
          apply True.intro
        let assump_35 := assump_2 assump_40
        apply False.elim assump_35


variable (p4 p5 p2 p7 : Prop)
theorem file47_16028 : (((((False → False) → False) ∨ ((True ∨ p7) → False)) ∧ (((False ∧ p7) ∨ (p4 → p5)) ∨ ((p7 ∨ p2) → (p7 ∧ p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_12
        case inr assump_11 =>
          have assump_60 : (False → False) := by
            intro assump_20
            apply False.elim assump_20
          let assump_19 := assump_4 assump_60
          apply False.elim assump_19
      case inr assump_9 =>
        have assump_61 : (False → False) := by
          intro assump_30
          apply False.elim assump_30
        let assump_29 := assump_4 assump_61
        apply False.elim assump_29
    case inr assump_5 =>
      cases assump_3
      case inl assump_38 =>
        cases assump_38
        case inl assump_40 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            apply False.elim assump_42
        case inr assump_41 =>
          have assump_62 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_49 := assump_5 assump_62
          apply False.elim assump_49
      case inr assump_39 =>
        have assump_63 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_56 := assump_5 assump_63
        apply False.elim assump_56


variable (p7 p4 p2 p6 p5 p3 p0 : Prop)
theorem file47_17634 : ((((((p3 → False) → (p7 ∨ False)) → False) → (((p0 ∧ p0) → (p2 ∧ p4)) ∧ ((p6 → False) → (False ∨ p3)))) ∧ ((((p3 → p0) → False) → False) ∧ (((p5 → False) → (False → p3)) → False))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      have assump_26 : ((p5 → False) → (False → p3)) := by
        intro assump_19
        intro assump_20
        apply False.elim assump_20
      let assump_18 := assump_13 assump_26
      apply False.elim assump_18


variable (p5 p7 p6 p4 p2 p0 p3 p1 : Prop)
theorem file47_18239 : ((((((p6 ∨ p4) ∧ (False ∧ p7)) ∧ ((False ∧ p6) ∧ (p2 ∨ False))) ∧ (((p3 ∨ p7) → (p6 ∧ p3)) ∨ ((p5 ∨ p3) → (p4 ∨ p3)))) ∧ ((((p2 ∧ p3) ∧ (p6 ∧ p7)) ∧ ((p7 ∧ False) ∧ (p2 → p5))) ∧ (((p5 → False) ∧ (p5 → p0)) ∨ ((p1 → False) → (p0 ∨ p1))))) → False) := by
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
          case inl assump_10 =>
            cases assump_9
            case intro assump_14 assump_15 =>
              apply False.elim assump_14
          case inr assump_11 =>
            cases assump_9
            case intro assump_20 assump_21 =>
              apply False.elim assump_20


variable (p7 p5 p6 p2 p1 : Prop)
theorem file47_19112 : (((((p6 → False) → (p6 → False)) ∨ ((p1 → False) → (p1 → False))) → False) → ((((p6 → p6) ∨ (p2 ∧ p5)) ∨ ((False ∧ p1) → False)) ∨ (((False → p7) ∧ (True ∧ True)) ∨ ((False ∨ p1) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_4
  exact assump_4


variable (p0 p5 p2 p3 p6 p7 p4 : Prop)
theorem file47_19468 : (((((False → p5) ∧ (p2 ∨ p4)) ∧ ((p6 ∨ p4) ∨ (p7 → p0))) ∧ (((p3 → p6) → (p0 → True)) → False)) → ((((p7 ∨ p6) → (p2 ∨ p5)) → False) → (((p0 ∧ p2) ∨ (p4 → False)) → ((p4 → False) ∨ (p6 ∧ p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_19
            case inl assump_22 =>
              cases assump_17
              case inl assump_26 =>
                cases assump_26
                case inl assump_28 =>
                  apply Or.inl
                  intro assump_34
                  have assump_230 : ((p3 → p6) → (p0 → True)) := by
                    intro assump_39
                    intro assump_40
                    apply True.intro
                  let assump_38 := assump_15 assump_230
                  apply False.elim assump_38
                case inr assump_29 =>
                  apply Or.inl
                  intro assump_48
                  have assump_231 : ((p3 → p6) → (p0 → True)) := by
                    intro assump_53
                    intro assump_54
                    apply True.intro
                  let assump_52 := assump_15 assump_231
                  apply False.elim assump_52
              case inr assump_27 =>
                apply Or.inl
                intro assump_62
                have assump_232 : ((p3 → p6) → (p0 → True)) := by
                  intro assump_67
                  intro assump_68
                  apply True.intro
                let assump_66 := assump_15 assump_232
                apply False.elim assump_66
            case inr assump_23 =>
              cases assump_17
              case inl assump_74 =>
                cases assump_74
                case inl assump_76 =>
                  apply Or.inl
                  intro assump_82
                  have assump_233 : ((p3 → p6) → (p0 → True)) := by
                    intro assump_87
                    intro assump_88
                    apply True.intro
                  let assump_86 := assump_15 assump_233
                  apply False.elim assump_86
                case inr assump_77 =>
                  apply Or.inl
                  intro assump_96
                  have assump_234 : ((p3 → p6) → (p0 → True)) := by
                    intro assump_101
                    intro assump_102
                    apply True.intro
                  let assump_100 := assump_15 assump_234
                  apply False.elim assump_100
              case inr assump_75 =>
                apply Or.inl
                intro assump_110
                have assump_235 : ((p3 → p6) → (p0 → True)) := by
                  intro assump_115
                  intro assump_116
                  apply True.intro
                let assump_114 := assump_15 assump_235
                apply False.elim assump_114
  case inr assump_5 =>
    cases assump_1
    case intro assump_124 assump_125 =>
      cases assump_124
      case intro assump_126 assump_127 =>
        cases assump_126
        case intro assump_128 assump_129 =>
          cases assump_129
          case inl assump_132 =>
            cases assump_127
            case inl assump_136 =>
              cases assump_136
              case inl assump_138 =>
                apply Or.inl
                intro assump_144
                have assump_236 : ((p3 → p6) → (p0 → True)) := by
                  intro assump_149
                  intro assump_150
                  apply True.intro
                let assump_148 := assump_125 assump_236
                apply False.elim assump_148
              case inr assump_139 =>
                apply Or.inl
                intro assump_158
                have assump_237 : ((p3 → p6) → (p0 → True)) := by
                  intro assump_163
                  intro assump_164
                  apply True.intro
                let assump_162 := assump_125 assump_237
                apply False.elim assump_162
            case inr assump_137 =>
              apply Or.inl
              intro assump_172
              have assump_238 : ((p3 → p6) → (p0 → True)) := by
                intro assump_177
                intro assump_178
                apply True.intro
              let assump_176 := assump_125 assump_238
              apply False.elim assump_176
          case inr assump_133 =>
            cases assump_127
            case inl assump_184 =>
              cases assump_184
              case inl assump_186 =>
                apply Or.inl
                intro assump_192
                have assump_239 : ((p3 → p6) → (p0 → True)) := by
                  intro assump_197
                  intro assump_198
                  apply True.intro
                let assump_196 := assump_125 assump_239
                apply False.elim assump_196
              case inr assump_187 =>
                apply Or.inl
                intro assump_206
                have assump_240 : ((p3 → p6) → (p0 → True)) := by
                  intro assump_211
                  intro assump_212
                  apply True.intro
                let assump_210 := assump_125 assump_240
                apply False.elim assump_210
            case inr assump_185 =>
              apply Or.inl
              intro assump_220
              have assump_241 : ((p3 → p6) → (p0 → True)) := by
                intro assump_225
                intro assump_226
                apply True.intro
              let assump_224 := assump_125 assump_241
              apply False.elim assump_224


variable (p2 p4 p1 p5 p3 p7 : Prop)
theorem file47_25306 : (((((p2 ∨ p1) → (p3 ∨ p5)) ∧ ((True ∨ True) → (p4 → False))) ∨ (((p5 ∧ p2) ∨ (p2 → True)) → False)) → ((((p5 → False) ∧ (p5 ∨ p4)) → False) ∧ (((p5 ∨ p2) → (p5 ∨ p2)) ∨ ((p3 ∧ p7) → (p1 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          have assump_80 : p5 := by
            exact assump_7
          let assump_23 := assump_3 assump_80
          apply False.elim assump_23
      case inr assump_12 =>
        have assump_81 : ((p5 ∧ p2) ∨ (p2 → True)) := by
          apply Or.inr
          intro assump_30
          apply True.intro
        let assump_29 := assump_12 assump_81
        apply False.elim assump_29
    case inr assump_8 =>
      cases assump_1
      case inl assump_36 =>
        cases assump_36
        case intro assump_38 assump_39 =>
          have assump_82 : (True ∨ True) := by
            apply Or.inl
            apply True.intro
          let assump_44 := assump_39 assump_82
          have assump_83 : p4 := by
            exact assump_8
          let assump_45 := assump_44 assump_83
          apply False.elim assump_45
      case inr assump_37 =>
        have assump_84 : ((p5 ∧ p2) ∨ (p2 → True)) := by
          apply Or.inr
          intro assump_52
          apply True.intro
        let assump_51 := assump_37 assump_84
        apply False.elim assump_51
  cases assump_1
  case inl assump_56 =>
    cases assump_56
    case intro assump_58 assump_59 =>
      apply Or.inl
      intro assump_64
      cases assump_64
      case inl assump_65 =>
        apply Or.inl
        exact assump_65
      case inr assump_66 =>
        apply Or.inr
        exact assump_66
  case inr assump_57 =>
    apply Or.inl
    intro assump_73
    cases assump_73
    case inl assump_74 =>
      apply Or.inl
      exact assump_74
    case inr assump_75 =>
      apply Or.inr
      exact assump_75


variable (p0 p6 p1 p4 p7 p2 p5 p3 : Prop)
theorem file47_27425 : ((((((p5 ∨ False) ∨ (p1 → False)) ∧ ((p5 ∨ p3) → (False ∨ p5))) ∧ (((p3 → False) ∧ (p6 ∧ False)) ∧ ((True ∨ p2) → (p1 ∧ p0)))) ∨ ((((False ∧ True) → (p2 ∨ p7)) ∨ ((p6 → p4) ∧ (p6 → True))) → (((False → False) ∨ (p3 ∧ p3)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_5
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_19
                case intro assump_22 assump_23 =>
                  apply False.elim assump_23
          case inr assump_11 =>
            apply False.elim assump_11
        case inr assump_9 =>
          cases assump_5
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              cases assump_37
              case intro assump_40 assump_41 =>
                apply False.elim assump_41
  case inr assump_3 =>
    have assump_61 : (((False ∧ True) → (p2 ∨ p7)) ∨ ((p6 → p4) ∧ (p6 → True))) := by
      apply Or.inl
      intro assump_49
      cases assump_49
      case intro assump_50 assump_51 =>
        apply False.elim assump_50
    let assump_48 := assump_3 assump_61
    have assump_62 : ((False → False) ∨ (p3 ∧ p3)) := by
      apply Or.inl
      intro assump_55
      apply False.elim assump_55
    let assump_54 := assump_48 assump_62
    apply False.elim assump_54


variable (p3 p1 p2 p6 p4 p5 : Prop)
theorem file47_29145 : ((((((p4 ∨ p1) → False) ∨ ((p5 → p3) ∧ (p6 → False))) → (((p6 → False) ∨ (p2 → False)) → ((p4 ∧ p2) → (p2 ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_43 : ((((p4 ∨ p1) → False) ∨ ((p5 → p3) ∧ (p6 → False))) → (((p6 → False) ∨ (p2 → False)) → ((p4 ∧ p2) → (p2 ∨ p2)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_6
      case inl assump_14 =>
        cases assump_5
        case inl assump_18 =>
          apply Or.inl
          exact assump_9
        case inr assump_19 =>
          cases assump_19
          case intro assump_22 assump_23 =>
            apply Or.inl
            exact assump_9
      case inr assump_15 =>
        cases assump_5
        case inl assump_30 =>
          apply Or.inl
          exact assump_9
        case inr assump_31 =>
          cases assump_31
          case intro assump_34 assump_35 =>
            apply Or.inl
            exact assump_9
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p6 p1 p3 p2 p7 p5 p4 : Prop)
theorem file47_30262 : (((((p1 → False) → (False ∨ p7)) ∨ ((p7 → p4) ∧ (p3 ∨ p3))) → (((p5 → p6) ∨ (p1 ∨ False)) → ((p5 ∨ p7) ∨ (False → p4)))) ∨ ((((False → p3) → (p2 → False)) ∨ ((False ∧ True) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      apply Or.inr
      intro assump_11
      apply False.elim assump_11
    case inr assump_8 =>
      cases assump_8
      case intro assump_14 assump_15 =>
        cases assump_15
        case inl assump_18 =>
          apply Or.inr
          intro assump_22
          apply False.elim assump_22
        case inr assump_19 =>
          apply Or.inr
          intro assump_27
          apply False.elim assump_27
  case inr assump_4 =>
    cases assump_4
    case inl assump_30 =>
      cases assump_1
      case inl assump_34 =>
        apply Or.inr
        intro assump_38
        apply False.elim assump_38
      case inr assump_35 =>
        cases assump_35
        case intro assump_41 assump_42 =>
          cases assump_42
          case inl assump_45 =>
            apply Or.inr
            intro assump_49
            apply False.elim assump_49
          case inr assump_46 =>
            apply Or.inr
            intro assump_54
            apply False.elim assump_54
    case inr assump_31 =>
      apply False.elim assump_31


variable (p5 p4 p3 p0 p2 : Prop)
theorem file47_31691 : ((((((p5 ∧ p4) ∧ (p4 → p2)) ∨ ((p3 → p0) → (p3 → p5))) ∨ (((p5 ∧ p0) ∧ (p3 ∧ p5)) ∧ ((p3 → False) ∨ (p3 ∧ p4)))) ∧ ((((False ∧ False) → False) ∨ ((False → True) ∧ (p0 → False))) → False)) → False) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_25
    case inl assump_27 =>
      cases assump_27
      case inl assump_29 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          cases assump_31
          case intro assump_33 assump_34 =>
            have assump_113 : (((False ∧ False) → False) ∨ ((False → True) ∧ (p0 → False))) := by
              apply Or.inl
              intro assump_44
              cases assump_44
              case intro assump_45 assump_46 =>
                apply False.elim assump_45
            let assump_43 := assump_26 assump_113
            apply False.elim assump_43
      case inr assump_30 =>
        have assump_114 : (((False ∧ False) → False) ∨ ((False → True) ∧ (p0 → False))) := by
          apply Or.inl
          intro assump_57
          cases assump_57
          case intro assump_58 assump_59 =>
            apply False.elim assump_58
        let assump_56 := assump_26 assump_114
        apply False.elim assump_56
    case inr assump_28 =>
      cases assump_28
      case intro assump_65 assump_66 =>
        cases assump_65
        case intro assump_67 assump_68 =>
          cases assump_67
          case intro assump_69 assump_70 =>
            cases assump_68
            case intro assump_75 assump_76 =>
              cases assump_66
              case inl assump_81 =>
                have assump_115 : (((False ∧ False) → False) ∨ ((False → True) ∧ (p0 → False))) := by
                  apply Or.inl
                  intro assump_88
                  cases assump_88
                  case intro assump_89 assump_90 =>
                    apply False.elim assump_89
                let assump_87 := assump_26 assump_115
                apply False.elim assump_87
              case inr assump_82 =>
                cases assump_82
                case intro assump_96 assump_97 =>
                  have assump_116 : (((False ∧ False) → False) ∨ ((False → True) ∧ (p0 → False))) := by
                    apply Or.inl
                    intro assump_105
                    cases assump_105
                    case intro assump_106 assump_107 =>
                      apply False.elim assump_106
                  let assump_104 := assump_26 assump_116
                  apply False.elim assump_104


variable (p3 : Prop)
theorem file47_34268 : (((((p3 → p3) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : (((p3 → p3) → False) → False) := by
    intro assump_5
    have assump_19 : (p3 → p3) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p0 p5 p6 p7 : Prop)
theorem file47_34685 : (((((p6 → False) ∧ (p5 → False)) ∧ ((p6 → False) → (False ∧ p0))) ∧ (((p0 → p7) → (p5 ∨ p5)) ∨ ((p2 → False) → False))) → ((((p7 ∧ False) ∧ (True ∧ False)) → False) ∨ (((True → p5) → False) → ((p5 → p5) → (p6 ∧ p5))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case inl assump_14 =>
          apply Or.inl
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              apply False.elim assump_22
        case inr assump_15 =>
          apply Or.inl
          intro assump_29
          cases assump_29
          case intro assump_30 assump_31 =>
            cases assump_30
            case intro assump_32 assump_33 =>
              apply False.elim assump_33


variable (p2 p4 p0 p1 p7 p6 p5 : Prop)
theorem file47_35706 : ((((((p7 → p1) → (False → p2)) ∨ ((p0 → True) → (p5 ∨ p4))) ∨ (((p7 ∨ True) ∨ (p2 ∨ p6)) ∧ ((p7 → False) → (False → p1)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p7 → p1) → (False → p2)) ∨ ((p0 → True) → (p5 ∨ p4))) ∨ (((p7 ∨ True) ∨ (p2 ∨ p6)) ∧ ((p7 → False) → (False → p1)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p4 p0 p1 p5 p6 : Prop)
theorem file47_36240 : (((((p1 ∧ p4) → (False ∧ p6)) ∧ ((p4 → False) ∧ (p0 ∨ p5))) ∧ (((True → False) → (p4 → p4)) → ((True ∧ False) ∧ (False → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_48 : ((True → False) → (p4 → p4)) := by
            intro assump_19
            intro assump_20
            exact assump_20
          let assump_18 := assump_3 assump_48
          let assump_25 := And.left assump_18
          let assump_26 := And.right assump_25
          apply False.elim assump_26
        case inr assump_13 =>
          have assump_49 : ((True → False) → (p4 → p4)) := by
            intro assump_36
            intro assump_37
            exact assump_37
          let assump_35 := assump_3 assump_49
          let assump_42 := And.left assump_35
          let assump_43 := And.right assump_42
          apply False.elim assump_43


variable (p3 p4 p6 p5 p0 p7 p2 p1 : Prop)
theorem file47_37361 : (((((p3 ∧ p1) → False) → ((p6 → False) → False)) → (((p1 ∧ p2) → (p6 → p6)) ∧ ((True ∧ p6) ∨ (p1 ∧ True)))) → ((((True ∧ False) → (p5 → p4)) ∨ ((p5 ∨ p7) ∧ (p3 → p1))) ∨ (((p4 → p0) ∨ (p6 → False)) ∨ ((p1 → p3) → (p1 ∧ p2))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_9


variable (p7 p0 p3 p1 p4 p5 p6 p2 : Prop)
theorem file47_37822 : (((((p7 → p4) ∨ (p5 ∨ False)) ∨ ((p3 → p6) → False)) ∧ (((p1 → p4) ∧ (p0 → p3)) ∨ ((p7 ∧ p2) → False))) → ((((False ∧ False) ∧ (p3 ∨ p7)) → ((p3 → p3) → (False ∨ p3))) ∨ (((p6 ∨ True) ∨ (p7 → p1)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply Or.inl
            intro assump_18
            intro assump_19
            cases assump_18
            case intro assump_22 assump_23 =>
              cases assump_22
              case intro assump_24 assump_25 =>
                apply False.elim assump_24
        case inr assump_11 =>
          apply Or.inl
          intro assump_30
          intro assump_31
          cases assump_30
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              apply False.elim assump_36
      case inr assump_7 =>
        cases assump_7
        case inl assump_40 =>
          cases assump_3
          case inl assump_44 =>
            cases assump_44
            case intro assump_46 assump_47 =>
              apply Or.inl
              intro assump_52
              intro assump_53
              cases assump_52
              case intro assump_56 assump_57 =>
                cases assump_56
                case intro assump_58 assump_59 =>
                  apply False.elim assump_58
          case inr assump_45 =>
            apply Or.inl
            intro assump_64
            intro assump_65
            cases assump_64
            case intro assump_68 assump_69 =>
              cases assump_68
              case intro assump_70 assump_71 =>
                apply False.elim assump_70
        case inr assump_41 =>
          apply False.elim assump_41
    case inr assump_5 =>
      cases assump_3
      case inl assump_78 =>
        cases assump_78
        case intro assump_80 assump_81 =>
          apply Or.inl
          intro assump_86
          intro assump_87
          cases assump_86
          case intro assump_90 assump_91 =>
            cases assump_90
            case intro assump_92 assump_93 =>
              apply False.elim assump_92
      case inr assump_79 =>
        apply Or.inl
        intro assump_98
        intro assump_99
        cases assump_98
        case intro assump_102 assump_103 =>
          cases assump_102
          case intro assump_104 assump_105 =>
            apply False.elim assump_104


variable (p6 p3 p2 p4 : Prop)
theorem file47_40495 : (((((p4 ∨ p6) → False) → ((p4 → p6) ∨ (p6 → False))) → False) → ((((True → False) ∧ (p6 → False)) ∨ ((p3 ∧ p6) → False)) ∨ (((p2 ∧ True) → (p4 ∨ False)) ∧ ((p3 → p2) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_36 : (((p4 ∨ p6) → False) → ((p4 → p6) ∨ (p6 → False))) := by
    intro assump_8
    apply Or.inl
    intro assump_11
    have assump_37 : (p4 ∨ p6) := by
      apply Or.inl
      exact assump_11
    let assump_15 := assump_8 assump_37
    apply False.elim assump_15
  let assump_7 := assump_1 assump_36
  apply False.elim assump_7
  intro assump_22
  have assump_38 : (((p4 ∨ p6) → False) → ((p4 → p6) ∨ (p6 → False))) := by
    intro assump_27
    apply Or.inl
    intro assump_30
    exact assump_22
  let assump_26 := assump_1 assump_38
  apply False.elim assump_26


variable (p6 p4 p1 p2 p0 p3 : Prop)
theorem file47_41405 : ((((((False → False) → False) → ((p2 → p0) ∧ (p1 → False))) ∨ (((p0 ∨ p2) → (p3 ∨ True)) ∨ ((p4 ∨ p6) ∨ (p6 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((False → False) → False) → ((p2 → p0) ∧ (p1 → False))) ∨ (((p0 ∨ p2) → (p3 ∨ True)) ∨ ((p4 ∨ p6) ∨ (p6 ∨ p3)))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    intro assump_6
    have assump_34 : (False → False) := by
      intro assump_12
      apply False.elim assump_12
    let assump_11 := assump_5 assump_34
    apply False.elim assump_11
    intro assump_18
    have assump_35 : (False → False) := by
      intro assump_24
      apply False.elim assump_24
    let assump_23 := assump_5 assump_35
    apply False.elim assump_23
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p0 p5 p1 p6 p7 : Prop)
theorem file47_42258 : (((((p5 ∧ p6) ∨ (p0 → p1)) ∨ ((p6 ∧ p1) → False)) ∧ (((p7 ∧ p6) → False) ∧ ((p1 ∧ p6) ∧ (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                have assump_72 : True := by
                  apply True.intro
                let assump_28 := assump_19 assump_72
                apply False.elim assump_28
      case inr assump_7 =>
        cases assump_3
        case intro assump_34 assump_35 =>
          cases assump_35
          case intro assump_38 assump_39 =>
            cases assump_38
            case intro assump_40 assump_41 =>
              have assump_73 : True := by
                apply True.intro
              let assump_48 := assump_39 assump_73
              apply False.elim assump_48
    case inr assump_5 =>
      cases assump_3
      case intro assump_54 assump_55 =>
        cases assump_55
        case intro assump_58 assump_59 =>
          cases assump_58
          case intro assump_60 assump_61 =>
            have assump_74 : True := by
              apply True.intro
            let assump_68 := assump_59 assump_74
            apply False.elim assump_68


variable (p5 p0 p7 : Prop)
theorem file47_43833 : (((((p5 ∧ p5) ∨ (p0 → False)) → ((p7 → False) → (p5 → False))) ∧ (((p0 → True) → (p5 ∨ p0)) ∧ ((p7 → p7) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_19 : (p7 → p7) := by
        intro assump_13
        exact assump_13
      let assump_12 := assump_7 assump_19
      apply False.elim assump_12


variable (p0 p5 p2 p7 p1 : Prop)
theorem file47_44306 : ((((((True → False) → (p5 → p1)) → False) → (((p2 → p0) → (p1 ∨ p7)) → ((p1 ∨ p1) → False))) → False) → False) := by
  intro assump_9
  have assump_53 : ((((True → False) → (p5 → p1)) → False) → (((p2 → p0) → (p1 ∨ p7)) → ((p1 ∨ p1) → False))) := by
    intro assump_13
    intro assump_14
    intro assump_15
    cases assump_15
    case inl assump_16 =>
      have assump_54 : ((True → False) → (p5 → p1)) := by
        intro assump_25
        intro assump_26
        exact assump_16
      let assump_24 := assump_13 assump_54
      apply False.elim assump_24
    case inr assump_17 =>
      have assump_55 : ((True → False) → (p5 → p1)) := by
        intro assump_41
        intro assump_42
        exact assump_17
      let assump_40 := assump_13 assump_55
      apply False.elim assump_40
  let assump_12 := assump_9 assump_53
  apply False.elim assump_12


variable (p7 p4 p6 p0 p5 : Prop)
theorem file47_45224 : ((((((p5 ∨ p5) ∨ (p6 ∨ True)) ∨ ((p4 ∨ p4) → False)) ∨ (((p0 ∨ p4) → (p7 → p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p5 ∨ p5) ∨ (p6 ∨ True)) ∨ ((p4 ∨ p4) → False)) ∨ (((p0 ∨ p4) → (p7 → p7)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p1 p4 p3 p0 p5 p6 : Prop)
theorem file47_45680 : (((((p4 → True) ∧ (p6 ∧ p0)) → False) → (((p4 ∨ True) → False) → False)) ∨ ((((p6 → p6) → False) → False) → (((p1 → p6) ∧ (p3 ∧ p1)) ∨ ((p3 → False) ∨ (True ∧ p5))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_13 : (p4 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_9 := assump_2 assump_13
  apply False.elim assump_9


variable (p5 p1 p6 p3 p7 p0 p4 p2 : Prop)
theorem file47_46108 : (((((p6 ∧ False) → False) ∨ ((False ∧ p4) ∧ (True ∨ p0))) → (((False ∨ p6) ∧ (p1 → False)) → ((True → True) → (p1 → False)))) ∨ ((((True → False) ∧ (p4 ∨ p6)) ∧ ((True ∧ p5) ∨ (p7 → False))) → (((p2 → p3) → False) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      apply False.elim assump_11
    case inr assump_12 =>
      cases assump_1
      case inl assump_19 =>
        have assump_34 : p1 := by
          exact assump_4
        let assump_24 := assump_10 assump_34
        apply False.elim assump_24
      case inr assump_20 =>
        cases assump_20
        case intro assump_28 assump_29 =>
          cases assump_28
          case intro assump_30 assump_31 =>
            apply False.elim assump_30


variable (p1 p7 p6 p0 p2 : Prop)
theorem file47_47026 : (((((True → False) → (p0 → False)) ∧ ((p6 → True) ∨ (p2 → p1))) ∧ (((p1 ∨ p2) → (p6 → False)) ∧ ((True ∨ p7) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          have assump_34 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_18 := assump_13 assump_34
          apply False.elim assump_18
      case inr assump_9 =>
        cases assump_3
        case intro assump_24 assump_25 =>
          have assump_35 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_30 := assump_25 assump_35
          apply False.elim assump_30


variable (p6 p1 p0 p4 p2 p7 : Prop)
theorem file47_47915 : ((((((p7 → p0) → (p2 ∧ p6)) ∧ ((p6 ∧ p1) ∧ (p6 ∨ p7))) ∨ (((p0 → p1) ∧ (p7 ∨ p0)) → ((p2 → False) ∧ (p4 → p1)))) ∧ ((((p6 → False) → False) → False) ∧ (((p6 ∧ p7) ∧ (p6 → p6)) ∧ ((p1 → p2) ∨ (p1 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_11
            case inl assump_18 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case intro assump_30 assump_31 =>
                      cases assump_27
                      case inl assump_38 =>
                        have assump_166 : ((p6 → False) → False) := by
                          intro assump_49
                          have assump_167 : p6 := by
                            exact assump_30
                          let assump_52 := assump_49 assump_167
                          apply False.elim assump_52
                        let assump_48 := assump_22 assump_166
                        apply False.elim assump_48
                      case inr assump_39 =>
                        have assump_168 : p1 := by
                          exact assump_13
                        let assump_61 := assump_39 assump_168
                        apply False.elim assump_61
            case inr assump_19 =>
              cases assump_3
              case intro assump_67 assump_68 =>
                cases assump_68
                case intro assump_71 assump_72 =>
                  cases assump_71
                  case intro assump_73 assump_74 =>
                    cases assump_73
                    case intro assump_75 assump_76 =>
                      cases assump_72
                      case inl assump_83 =>
                        have assump_169 : ((p6 → False) → False) := by
                          intro assump_94
                          have assump_170 : p6 := by
                            exact assump_75
                          let assump_97 := assump_94 assump_170
                          apply False.elim assump_97
                        let assump_93 := assump_67 assump_169
                        apply False.elim assump_93
                      case inr assump_84 =>
                        have assump_171 : p1 := by
                          exact assump_13
                        let assump_106 := assump_84 assump_171
                        apply False.elim assump_106
    case inr assump_5 =>
      cases assump_3
      case intro assump_112 assump_113 =>
        cases assump_113
        case intro assump_116 assump_117 =>
          cases assump_116
          case intro assump_118 assump_119 =>
            cases assump_118
            case intro assump_120 assump_121 =>
              cases assump_117
              case inl assump_128 =>
                have assump_172 : ((p6 → False) → False) := by
                  intro assump_138
                  have assump_173 : p6 := by
                    exact assump_120
                  let assump_141 := assump_138 assump_173
                  apply False.elim assump_141
                let assump_137 := assump_112 assump_172
                apply False.elim assump_137
              case inr assump_129 =>
                have assump_174 : ((p6 → False) → False) := by
                  intro assump_156
                  have assump_175 : p6 := by
                    exact assump_120
                  let assump_159 := assump_156 assump_175
                  apply False.elim assump_159
                let assump_155 := assump_112 assump_174
                apply False.elim assump_155


variable (p3 p0 p6 p5 p7 p1 p2 : Prop)
theorem file47_51999 : (((((p3 ∧ p0) ∨ (p1 ∧ p7)) → ((p5 → False) → (p6 → False))) → (((True → False) ∧ (p3 → False)) → False)) ∨ ((((p0 ∨ p6) ∧ (p6 ∧ p6)) ∨ ((p2 → False) ∧ (p6 ∧ True))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_17 : True := by
      apply True.intro
    let assump_13 := assump_3 assump_17
    apply False.elim assump_13


variable (p2 p1 p0 p4 p6 p5 p3 p7 : Prop)
theorem file47_52472 : ((((((p2 → p3) → (p1 ∨ p2)) ∨ ((p2 ∨ p2) ∧ (p4 → p2))) → False) ∧ ((((p6 → p4) ∧ (False ∧ p0)) ∧ ((p0 ∨ p7) → (True → p7))) ∧ (((p6 → p3) → (True → False)) ∨ ((p5 → False) ∧ (False → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            apply False.elim assump_14


variable (p4 p7 p6 p0 p3 p2 p5 : Prop)
theorem file47_53100 : ((((((p3 → p5) → False) → False) ∧ (((p3 ∧ p0) ∨ (True → p6)) ∧ ((p7 ∨ p2) → (p7 → False)))) ∧ ((((p4 ∨ p4) → (True ∧ p4)) ∨ ((True ∧ p5) → (p7 ∨ p6))) → False)) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        cases assump_16
        case inl assump_18 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            have assump_58 : (((p4 ∨ p4) → (True ∧ p4)) ∨ ((True ∧ p5) → (p7 ∨ p6))) := by
              apply Or.inl
              intro assump_31
              apply And.intro
              apply True.intro
              cases assump_31
              case inl assump_32 =>
                exact assump_32
              case inr assump_33 =>
                exact assump_33
            let assump_30 := assump_11 assump_58
            apply False.elim assump_30
        case inr assump_19 =>
          have assump_59 : (((p4 ∨ p4) → (True ∧ p4)) ∨ ((True ∧ p5) → (p7 ∨ p6))) := by
            apply Or.inl
            intro assump_48
            apply And.intro
            apply True.intro
            cases assump_48
            case inl assump_49 =>
              exact assump_49
            case inr assump_50 =>
              exact assump_50
          let assump_47 := assump_11 assump_59
          apply False.elim assump_47


variable (p4 p5 p7 p0 p3 : Prop)
theorem file47_54580 : ((((((False ∧ True) ∧ (p3 → p3)) ∨ ((p7 ∨ p4) ∨ (False ∧ p0))) → (((True ∨ p5) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_42 : ((((False ∧ True) ∧ (p3 → p3)) ∨ ((p7 ∨ p4) ∨ (False ∧ p0))) → (((True ∨ p5) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
    case inr assump_10 =>
      cases assump_10
      case inl assump_17 =>
        cases assump_17
        case inl assump_19 =>
          have assump_43 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_24 := assump_6 assump_43
          apply False.elim assump_24
        case inr assump_20 =>
          have assump_44 : (True ∨ p5) := by
            apply Or.inl
            apply True.intro
          let assump_31 := assump_6 assump_44
          apply False.elim assump_31
      case inr assump_18 =>
        cases assump_18
        case intro assump_35 assump_36 =>
          apply False.elim assump_35
  let assump_4 := assump_1 assump_42
  apply False.elim assump_4


variable (p0 p5 p2 p3 p4 p6 p7 : Prop)
theorem file47_55869 : (((((p0 ∧ False) → (p7 → p5)) ∧ ((p4 → p7) ∨ (p2 → False))) → False) → ((((p3 ∧ p0) ∧ (p0 → False)) → ((p4 ∧ True) → (p3 ∧ p2))) ∨ (((p0 ∨ p5) → False) → ((p6 ∧ p5) ∧ (p3 → p3))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply And.intro
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_4
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        exact assump_14
  cases assump_5
  case intro assump_22 assump_23 =>
    cases assump_4
    case intro assump_28 assump_29 =>
      cases assump_28
      case intro assump_30 assump_31 =>
        have assump_42 : p0 := by
          exact assump_31
        let assump_38 := assump_29 assump_42
        apply False.elim assump_38


variable (p2 p7 p3 p0 p1 p6 p4 : Prop)
theorem file47_56709 : ((((((p4 ∨ p7) → False) ∧ ((True ∧ p3) → False)) ∨ (((p2 ∧ p7) ∨ (p4 ∨ p3)) → False)) ∧ ((((False → False) ∨ (True ∨ p3)) → ((False → False) → (p6 → p1))) ∧ (((p7 ∧ False) → (p3 → p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          have assump_54 : ((p7 ∧ False) → (p3 → p0)) := by
            intro assump_19
            intro assump_20
            cases assump_19
            case intro assump_23 assump_24 =>
              apply False.elim assump_24
          let assump_18 := assump_13 assump_54
          apply False.elim assump_18
    case inr assump_5 =>
      cases assump_3
      case intro assump_34 assump_35 =>
        have assump_55 : ((p7 ∧ False) → (p3 → p0)) := by
          intro assump_41
          intro assump_42
          cases assump_41
          case intro assump_45 assump_46 =>
            apply False.elim assump_46
        let assump_40 := assump_35 assump_55
        apply False.elim assump_40


variable (p1 p0 p6 p4 p3 p5 p7 p2 : Prop)
theorem file47_57922 : (((((p6 ∧ p1) ∨ (p5 → False)) → False) ∧ (((p7 ∧ p0) ∨ (p5 ∧ p5)) → False)) → ((((True ∧ p5) ∧ (True → False)) ∨ ((p4 ∨ p3) ∨ (p2 → p6))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          have assump_92 : ((p7 ∧ p0) ∨ (p5 ∧ p5)) := by
            apply Or.inr
            apply And.intro
            exact assump_8
            exact assump_8
          let assump_21 := assump_16 assump_92
          apply False.elim assump_21
  case inr assump_4 =>
    cases assump_4
    case inl assump_25 =>
      cases assump_25
      case inl assump_27 =>
        cases assump_1
        case intro assump_31 assump_32 =>
          have assump_93 : ((p6 ∧ p1) ∨ (p5 → False)) := by
            apply Or.inr
            intro assump_39
            have assump_94 : ((p7 ∧ p0) ∨ (p5 ∧ p5)) := by
              apply Or.inr
              apply And.intro
              exact assump_39
              exact assump_39
            let assump_43 := assump_32 assump_94
            apply False.elim assump_43
          let assump_38 := assump_31 assump_93
          apply False.elim assump_38
      case inr assump_28 =>
        cases assump_1
        case intro assump_52 assump_53 =>
          have assump_95 : ((p6 ∧ p1) ∨ (p5 → False)) := by
            apply Or.inr
            intro assump_60
            have assump_96 : ((p7 ∧ p0) ∨ (p5 ∧ p5)) := by
              apply Or.inr
              apply And.intro
              exact assump_60
              exact assump_60
            let assump_64 := assump_53 assump_96
            apply False.elim assump_64
          let assump_59 := assump_52 assump_95
          apply False.elim assump_59
    case inr assump_26 =>
      cases assump_1
      case intro assump_73 assump_74 =>
        have assump_97 : ((p6 ∧ p1) ∨ (p5 → False)) := by
          apply Or.inr
          intro assump_81
          have assump_98 : ((p7 ∧ p0) ∨ (p5 ∧ p5)) := by
            apply Or.inr
            apply And.intro
            exact assump_81
            exact assump_81
          let assump_85 := assump_74 assump_98
          apply False.elim assump_85
        let assump_80 := assump_73 assump_97
        apply False.elim assump_80


variable (p3 p5 p2 p0 p1 p7 p4 p6 : Prop)
theorem file47_60365 : ((((((False ∧ p1) → (p5 ∨ p5)) → ((p3 → False) ∧ (p2 → False))) ∧ (((p1 → p7) ∧ (p0 → False)) → ((p0 → False) ∨ (p4 ∨ p0)))) ∧ ((((p6 ∧ p6) ∨ (p5 ∧ p4)) ∨ ((True ∧ False) → (p5 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_26 : (((p6 ∧ p6) ∨ (p5 ∧ p4)) ∨ ((True ∧ False) → (p5 → False))) := by
        apply Or.inr
        intro assump_13
        intro assump_14
        cases assump_13
        case intro assump_17 assump_18 =>
          apply False.elim assump_18
      let assump_12 := assump_3 assump_26
      apply False.elim assump_12


variable (p1 p3 p7 p4 p2 p5 p6 p0 : Prop)
theorem file47_61103 : (((((p2 → False) → (p6 ∨ True)) ∨ ((p7 ∨ True) ∨ (p1 → p5))) ∨ (((True → p4) ∧ (p1 ∨ p0)) ∨ ((False ∧ p4) → False))) ∧ ((((p4 → False) → False) ∧ ((False → True) → (p4 → False))) → (((p5 ∨ p2) → False) → ((p7 → False) ∨ (p3 ∨ p4))))) := by
  apply And.intro
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply True.intro
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply Or.inl
    intro assump_14
    have assump_36 : (p4 → False) := by
      intro assump_22
      have assump_37 : (False → True) := by
        intro assump_28
        apply True.intro
      let assump_27 := assump_9 assump_37
      have assump_38 : p4 := by
        exact assump_22
      let assump_29 := assump_27 assump_38
      apply False.elim assump_29
    let assump_21 := assump_8 assump_36
    apply False.elim assump_21


variable (p4 p7 p0 p6 p1 p2 : Prop)
theorem file47_62024 : (((((p1 ∨ p0) → False) ∧ ((p4 ∨ p6) ∧ (False ∨ p7))) ∨ (((p7 ∧ p4) ∧ (p1 ∧ p1)) → ((True → p2) → False))) → ((((True ∨ True) ∨ (True ∨ p4)) ∨ ((False → p0) → False)) ∨ (((p6 → False) → (p7 ∧ p6)) ∧ ((p0 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case inl assump_14 =>
            apply False.elim assump_14
          case inr assump_15 =>
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply True.intro
        case inr assump_11 =>
          cases assump_9
          case inl assump_22 =>
            apply False.elim assump_22
          case inr assump_23 =>
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro


variable (p1 p3 p7 p4 p2 p5 : Prop)
theorem file47_63194 : (((((p2 → p3) → (p7 → p4)) → False) → (((p1 → False) → False) → ((p2 ∨ p5) ∨ (p4 → False)))) ∨ ((((p4 ∨ p3) ∧ (p7 ∨ p4)) → False) ∨ (((True → p4) ∨ (False → False)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inr
  intro assump_7
  have assump_21 : ((p2 → p3) → (p7 → p4)) := by
    intro assump_12
    intro assump_13
    exact assump_7
  let assump_11 := assump_1 assump_21
  apply False.elim assump_11


variable (p5 p3 p6 p1 p7 p4 p0 : Prop)
theorem file47_63695 : (((((True ∧ p1) ∧ (True ∨ p1)) ∨ ((p6 → p6) ∨ (p4 ∨ p7))) ∨ (((p7 ∧ p5) → (p0 → p3)) ∨ ((p1 ∧ p0) → False))) ∧ ((((p6 ∨ p5) ∧ (True ∧ p3)) → ((p6 ∨ p1) → (p6 → False))) → (((p0 → True) → (p3 → p3)) ∨ ((p0 ∧ p7) → False)))) := by
  apply And.intro
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_1
  exact assump_1
  intro assump_4
  apply Or.inl
  intro assump_7
  intro assump_8
  exact assump_8


variable (p6 p5 p7 p1 p4 p0 p3 : Prop)
theorem file47_64167 : ((((((p6 → p6) → (p1 → False)) → ((p7 ∨ p0) ∨ (p0 ∨ True))) ∧ (((p4 → False) ∨ (p4 ∧ True)) → ((p3 → True) ∧ (False ∨ p7)))) ∧ ((((p0 → False) ∧ (p0 → True)) ∧ ((False ∨ False) ∧ (p5 → p7))) ∧ (((p0 → p4) ∨ (p6 ∨ p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              cases assump_20
              case inl assump_22 =>
                apply False.elim assump_22
              case inr assump_23 =>
                apply False.elim assump_23


variable (p4 p1 p2 p0 p6 p5 p7 p3 : Prop)
theorem file47_65059 : (((((p2 → p3) ∧ (p6 → p4)) ∧ ((p2 → False) → (p0 → p1))) ∧ (((p4 → False) → False) ∧ ((True → p1) ∧ (p7 → False)))) → ((((p6 → False) ∧ (p5 → False)) → ((False ∧ False) → (p6 → p6))) ∨ (((p0 → p6) ∨ (p0 → p2)) ∧ ((p7 → False) → (p6 → p4))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            apply Or.inl
            intro assump_24
            intro assump_25
            intro assump_26
            cases assump_25
            case intro assump_29 assump_30 =>
              apply False.elim assump_29


variable (p2 p3 p6 p7 p4 p1 p5 p0 : Prop)
theorem file47_65914 : ((((((p3 ∧ p7) ∧ (False ∧ p6)) ∧ ((p3 → False) ∧ (p5 → p5))) ∧ (((False ∨ p6) ∧ (p0 → False)) → False)) ∧ ((((p3 ∨ True) → (p2 ∨ p1)) → ((p0 → False) → (p4 → p1))) → (((p2 → p5) ∧ (p7 ∧ True)) → ((p7 → True) ∧ (False → p2))))) → False) := by
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
              apply False.elim assump_16


variable (p2 p5 p1 p0 p4 : Prop)
theorem file47_66641 : ((((((p0 ∨ p5) ∨ (True ∧ p5)) → ((False ∨ p0) → (False → False))) → (((p2 ∧ p4) ∨ (True ∨ p1)) → ((p1 ∧ False) → False))) → False) → False) := by
  intro assump_5
  have assump_21 : ((((p0 ∨ p5) ∨ (True ∧ p5)) → ((False ∨ p0) → (False → False))) → (((p2 ∧ p4) ∨ (True ∨ p1)) → ((p1 ∧ False) → False))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      apply False.elim assump_13
  let assump_8 := assump_5 assump_21
  apply False.elim assump_8


variable (p7 p3 p1 p2 p4 p5 p6 : Prop)
theorem file47_67227 : ((((((p6 ∨ p3) ∧ (p2 ∨ p5)) → ((p6 → True) → False)) ∧ (((False ∨ True) → False) → False)) ∧ ((((p6 ∧ p4) → (p4 ∧ True)) ∧ ((p2 ∨ True) ∨ (p7 → p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_23 : (((p6 ∧ p4) → (p4 ∧ True)) ∧ ((p2 ∨ True) ∨ (p7 → p1))) := by
        apply And.intro
        intro assump_13
        apply And.intro
        cases assump_13
        case intro assump_14 assump_15 =>
          exact assump_15
        apply True.intro
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_12 := assump_3 assump_23
      apply False.elim assump_12


variable (p0 p1 p4 p6 p3 p2 : Prop)
theorem file47_68001 : (((((p4 ∧ False) ∨ (p6 → True)) → ((p1 ∧ p0) → (False → p0))) ∨ (((p0 → True) ∨ (p3 → True)) → False)) ∨ ((((p2 → p2) → (True ∧ p0)) → False) ∧ (((p2 ∧ p6) ∧ (p3 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply False.elim assump_3


variable (p7 p0 p3 p6 p1 p5 : Prop)
theorem file47_68359 : (((((p6 ∨ p1) → False) → ((p6 → p7) → (p7 → False))) ∨ (((p5 ∨ False) ∨ (p1 ∨ p6)) ∨ ((p0 → p7) ∨ (p7 → False)))) → ((((p5 ∨ p1) → (False ∧ p0)) → False) → (((p1 ∨ p3) → False) → ((False ∧ False) → (p6 ∨ p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p2 p7 p3 p1 p0 p6 : Prop)
theorem file47_68786 : ((((((True ∨ p1) ∨ (False → p7)) → ((p2 → p3) → (True → True))) ∨ (((p6 ∨ p0) → False) → ((False → False) ∨ (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((True ∨ p1) ∨ (False → p7)) → ((p2 → p3) → (True → True))) ∨ (((p6 ∨ p0) → False) → ((False → False) ∨ (p6 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p1 p7 p4 p6 p0 p3 : Prop)
theorem file47_69318 : (((((p7 → False) → (False → p4)) → ((p1 → False) → (p4 → p4))) ∨ (((p0 ∨ p4) ∧ (p0 ∧ p3)) → False)) ∨ ((((p6 ∨ p6) → False) → ((p1 ∧ p6) → (False → p7))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_23
  intro assump_24
  intro assump_25
  exact assump_25


variable (p4 p6 p3 p5 p1 p0 : Prop)
theorem file47_69650 : (((((False → p3) ∨ (p1 ∧ p4)) → False) ∧ (((p1 ∨ p5) → (True → False)) ∧ ((p6 → p0) ∧ (p0 → False)))) → False) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_14
    case intro assump_17 assump_18 =>
      cases assump_18
      case intro assump_21 assump_22 =>
        have assump_37 : ((False → p3) ∨ (p1 ∧ p4)) := by
          apply Or.inl
          intro assump_31
          apply False.elim assump_31
        let assump_30 := assump_13 assump_37
        apply False.elim assump_30


variable (p4 p0 p2 p1 p6 p5 p7 p3 : Prop)
theorem file47_70249 : (((((p3 → False) ∨ (False ∧ p0)) ∨ ((p5 ∨ p4) ∧ (p4 ∧ p6))) → (((p6 ∨ True) ∧ (p6 → True)) ∧ ((False ∧ p6) → False))) ∨ ((((p7 ∧ p1) → (p2 ∨ p6)) ∨ ((p6 ∨ p3) ∧ (False → p0))) → (((p3 → p3) ∧ (p1 → p4)) ∧ ((p1 → True) → False)))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inr
      apply True.intro
    case inr assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  case inr assump_3 =>
    cases assump_3
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        cases assump_13
        case intro assump_18 assump_19 =>
          apply Or.inl
          exact assump_19
      case inr assump_15 =>
        cases assump_13
        case intro assump_26 assump_27 =>
          apply Or.inl
          exact assump_27
  intro assump_32
  apply True.intro
  intro assump_33
  cases assump_33
  case intro assump_34 assump_35 =>
    apply False.elim assump_34


variable (p3 p4 p2 p5 p6 p7 p0 p1 : Prop)
theorem file47_71391 : ((((((True ∨ True) ∧ (True → p7)) → ((p3 → False) ∨ (p1 ∨ p1))) ∧ (((False ∧ p6) ∧ (p0 → False)) ∧ ((p5 ∨ False) ∨ (p3 → True)))) ∧ ((((p4 ∧ p7) → (p4 → p2)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_12


variable (p1 p7 p0 p5 p6 p4 : Prop)
theorem file47_71999 : ((((((p0 ∨ p4) ∨ (p4 → p0)) → False) → (((p1 → p5) → (p1 ∨ p0)) → ((p6 → False) ∨ (p7 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p0 ∨ p4) ∨ (p4 → p0)) → False) → (((p1 → p5) → (p1 ∨ p0)) → ((p6 → False) ∨ (p7 ∧ p4)))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    intro assump_11
    have assump_32 : ((p0 ∨ p4) ∨ (p4 → p0)) := by
      apply Or.inr
      intro assump_16
      have assump_33 : ((p0 ∨ p4) ∨ (p4 → p0)) := by
        apply Or.inl
        apply Or.inr
        exact assump_16
      let assump_21 := assump_5 assump_33
      apply False.elim assump_21
    let assump_15 := assump_5 assump_32
    apply False.elim assump_15
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p6 p5 p7 p4 p2 : Prop)
theorem file47_72807 : ((((((p6 → p2) → False) ∧ ((p7 → False) ∧ (p7 → False))) → (((p7 → False) ∧ (True ∧ p7)) → ((p6 ∨ p5) → (p2 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_65 : ((((p6 → p2) → False) ∧ ((p7 → False) ∧ (p7 → False))) → (((p7 → False) ∧ (True ∧ p7)) → ((p6 ∨ p5) → (p2 ∨ p4)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      cases assump_6
      case intro assump_12 assump_13 =>
        cases assump_13
        case intro assump_16 assump_17 =>
          cases assump_5
          case intro assump_22 assump_23 =>
            cases assump_23
            case intro assump_26 assump_27 =>
              have assump_66 : p7 := by
                exact assump_17
              let assump_32 := assump_27 assump_66
              apply False.elim assump_32
    case inr assump_9 =>
      cases assump_6
      case intro assump_38 assump_39 =>
        cases assump_39
        case intro assump_42 assump_43 =>
          cases assump_5
          case intro assump_48 assump_49 =>
            cases assump_49
            case intro assump_52 assump_53 =>
              have assump_67 : p7 := by
                exact assump_43
              let assump_58 := assump_53 assump_67
              apply False.elim assump_58
  let assump_4 := assump_1 assump_65
  apply False.elim assump_4


variable (p3 p6 p2 p4 p1 p7 : Prop)
theorem file47_74224 : (((((p4 ∨ False) ∧ (p3 ∧ False)) ∨ ((p1 ∧ p1) ∧ (p4 ∧ True))) ∨ (((False → p7) → False) → False)) ∨ ((((p7 ∨ p6) ∨ (p4 → p4)) ∨ ((p2 → False) → False)) → False)) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  have assump_11 : (False → p7) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p7 p3 p4 p2 p1 p0 : Prop)
theorem file47_74654 : ((((((p5 → False) → False) → ((p5 → False) → (p7 ∨ p3))) → (((True ∨ p0) → (True ∧ p2)) → False)) ∧ ((((p1 ∨ p4) → (False ∨ True)) ∧ ((p0 ∧ p4) ∧ (p3 ∧ p7))) ∧ (((p2 ∧ False) → (p0 → p7)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              have assump_42 : ((p2 ∧ False) → (p0 → p7)) := by
                intro assump_29
                intro assump_30
                cases assump_29
                case intro assump_33 assump_34 =>
                  apply False.elim assump_34
              let assump_28 := assump_7 assump_42
              apply False.elim assump_28


variable (p1 p5 p7 p2 : Prop)
theorem file47_75659 : (((((p2 → True) ∨ (p5 → p1)) ∨ ((p2 → p5) ∨ (p5 → p7))) → False) → False) := by
  intro assump_5
  have assump_13 : (((p2 → True) ∨ (p5 → p1)) ∨ ((p2 → p5) ∨ (p5 → p7))) := by
    apply Or.inl
    apply Or.inl
    intro assump_9
    apply True.intro
  let assump_8 := assump_5 assump_13
  apply False.elim assump_8


variable (p5 p7 p3 p0 : Prop)
theorem file47_76028 : (((((p0 → False) ∨ (p0 ∨ p3)) → ((p7 ∨ p0) ∨ (p7 → p5))) → False) → False) := by
  intro assump_1
  have assump_59 : (((p0 → False) ∨ (p0 ∨ p3)) → ((p7 ∨ p0) ∨ (p7 → p5))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inr
      intro assump_10
      have assump_60 : (((p0 → False) ∨ (p0 ∨ p3)) → ((p7 ∨ p0) ∨ (p7 → p5))) := by
        intro assump_16
        cases assump_16
        case inl assump_17 =>
          apply Or.inl
          apply Or.inl
          exact assump_10
        case inr assump_18 =>
          cases assump_18
          case inl assump_21 =>
            apply Or.inl
            apply Or.inl
            exact assump_10
          case inr assump_22 =>
            apply Or.inl
            apply Or.inl
            exact assump_10
      let assump_15 := assump_1 assump_60
      apply False.elim assump_15
    case inr assump_7 =>
      cases assump_7
      case inl assump_30 =>
        apply Or.inl
        apply Or.inr
        exact assump_30
      case inr assump_31 =>
        apply Or.inr
        intro assump_36
        have assump_61 : (((p0 → False) ∨ (p0 ∨ p3)) → ((p7 ∨ p0) ∨ (p7 → p5))) := by
          intro assump_42
          cases assump_42
          case inl assump_43 =>
            apply Or.inl
            apply Or.inl
            exact assump_36
          case inr assump_44 =>
            cases assump_44
            case inl assump_47 =>
              apply Or.inl
              apply Or.inl
              exact assump_36
            case inr assump_48 =>
              apply Or.inl
              apply Or.inl
              exact assump_36
        let assump_41 := assump_1 assump_61
        apply False.elim assump_41
  let assump_4 := assump_1 assump_59
  apply False.elim assump_4


variable (p5 p4 p7 p1 : Prop)
theorem file47_77850 : (((((p7 ∧ False) ∨ (p5 ∧ False)) ∧ ((p4 ∧ p7) → False)) ∧ (((p5 → False) ∨ (p5 → False)) ∨ ((p1 ∨ p4) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_9
      case inr assump_7 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply False.elim assump_15


variable (p7 p6 p0 p1 p3 p5 p4 : Prop)
theorem file47_78440 : ((((((p4 → p6) → (False → False)) → False) → (((p5 ∧ p3) → (p1 ∧ p6)) ∨ ((p0 → True) ∧ (p4 → p7)))) → False) → False) := by
  intro assump_1
  have assump_44 : ((((p4 → p6) → (False → False)) → False) → (((p5 ∧ p3) → (p1 ∧ p6)) ∨ ((p0 → True) ∧ (p4 → p7)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply And.intro
    cases assump_8
    case intro assump_9 assump_10 =>
      have assump_45 : ((p4 → p6) → (False → False)) := by
        intro assump_18
        intro assump_19
        apply False.elim assump_19
      let assump_17 := assump_5 assump_45
      apply False.elim assump_17
    cases assump_8
    case intro assump_25 assump_26 =>
      have assump_46 : ((p4 → p6) → (False → False)) := by
        intro assump_34
        intro assump_35
        apply False.elim assump_35
      let assump_33 := assump_5 assump_46
      apply False.elim assump_33
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


variable (p4 p6 p5 p1 : Prop)
theorem file47_79445 : ((((((p4 ∧ False) → False) ∧ ((p6 ∧ False) → (False ∧ True))) ∨ (((p1 → p4) → (p1 → p5)) → ((p6 → False) ∧ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p4 ∧ False) → False) ∧ ((p6 ∧ False) → (False ∧ True))) ∨ (((p1 → p4) → (p1 → p5)) → ((p6 → False) ∧ (True → False)))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
    intro assump_12
    apply And.intro
    cases assump_12
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
    apply True.intro
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p6 p1 p0 p7 p3 p5 p4 p2 : Prop)
theorem file47_80185 : (((((True ∧ p6) → (p5 → p5)) → ((True ∨ p1) → (p3 → p4))) → (((False → p3) → (p3 → p5)) → ((False ∨ p5) → False))) → ((((p3 → True) → False) → ((False → p0) → False)) ∨ (((p2 → p4) ∧ (False ∨ p0)) ∧ ((p5 → False) → (p2 → p7))))) := by
  intro assump_11
  apply Or.inl
  intro assump_14
  intro assump_15
  have assump_25 : (p3 → True) := by
    intro assump_21
    apply True.intro
  let assump_20 := assump_14 assump_25
  apply False.elim assump_20


variable (p3 p7 p2 p0 p5 p4 : Prop)
theorem file47_80695 : ((((((p3 ∧ p5) ∨ (p4 → p2)) → ((p5 → False) → (p5 → p0))) ∨ (((p5 → p4) ∨ (p7 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_36 : ((((p3 ∧ p5) ∨ (p4 → p2)) → ((p5 → False) → (p5 → p0))) ∨ (((p5 → p4) ∨ (p7 → False)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        have assump_37 : p5 := by
          exact assump_15
        let assump_22 := assump_6 assump_37
        apply False.elim assump_22
    case inr assump_13 =>
      have assump_38 : p5 := by
        exact assump_7
      let assump_29 := assump_6 assump_38
      apply False.elim assump_29
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p6 p2 p5 p3 p0 p7 p1 : Prop)
theorem file47_81559 : ((((((p3 ∧ p3) → (False → False)) → False) → False) ∧ ((((p5 → False) ∧ (False ∨ p7)) ∧ ((True ∧ False) ∧ (p5 ∧ p7))) ∧ (((True → p1) ∨ (p6 ∨ p5)) ∧ ((p3 ∧ True) ∧ (p0 ∨ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case inl assump_14 =>
            apply False.elim assump_14
          case inr assump_15 =>
            cases assump_9
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                apply False.elim assump_23


variable (p7 p6 p0 p2 p5 p3 p1 p4 : Prop)
theorem file47_82388 : (((((p3 → True) → (p1 ∧ p4)) ∧ ((False → False) ∨ (p6 → False))) → (((False → False) ∨ (True → False)) ∨ ((p6 → False) ∧ (p2 → p2)))) ∨ ((((p2 ∨ p7) ∨ (True ∨ p7)) → False) ∨ (((p4 ∨ p5) ∧ (p0 ∧ p4)) → ((False ∨ False) ∧ (p1 → p5))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      apply Or.inl
      intro assump_10
      apply False.elim assump_10
    case inr assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_15
      apply False.elim assump_15


variable (p2 p3 p6 p5 p7 p0 p1 : Prop)
theorem file47_83030 : (((((False ∨ p1) ∨ (p3 ∧ p2)) ∨ ((False ∨ p0) ∨ (p6 ∧ p7))) ∧ (((False ∧ p5) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          apply False.elim assump_8
        case inr assump_9 =>
          have assump_78 : ((False ∧ p5) → False) := by
            intro assump_17
            cases assump_17
            case intro assump_18 assump_19 =>
              apply False.elim assump_18
          let assump_16 := assump_3 assump_78
          apply False.elim assump_16
      case inr assump_7 =>
        cases assump_7
        case intro assump_25 assump_26 =>
          have assump_79 : ((False ∧ p5) → False) := by
            intro assump_34
            cases assump_34
            case intro assump_35 assump_36 =>
              apply False.elim assump_35
          let assump_33 := assump_3 assump_79
          apply False.elim assump_33
    case inr assump_5 =>
      cases assump_5
      case inl assump_42 =>
        cases assump_42
        case inl assump_44 =>
          apply False.elim assump_44
        case inr assump_45 =>
          have assump_80 : ((False ∧ p5) → False) := by
            intro assump_53
            cases assump_53
            case intro assump_54 assump_55 =>
              apply False.elim assump_54
          let assump_52 := assump_3 assump_80
          apply False.elim assump_52
      case inr assump_43 =>
        cases assump_43
        case intro assump_61 assump_62 =>
          have assump_81 : ((False ∧ p5) → False) := by
            intro assump_70
            cases assump_70
            case intro assump_71 assump_72 =>
              apply False.elim assump_71
          let assump_69 := assump_3 assump_81
          apply False.elim assump_69


variable (p0 p5 p6 p7 p4 p2 : Prop)
theorem file47_84987 : (((((p2 ∧ True) → (p5 ∨ p2)) ∨ ((True ∨ p2) → False)) ∧ (((p5 → p5) → (False ∧ True)) ∧ ((p6 ∧ p6) → False))) → ((((True ∨ p7) → (p5 → p6)) → ((p5 → p7) → (p0 → p6))) ∨ (((p6 ∨ True) → (p4 ∧ p2)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply Or.inl
        intro assump_14
        intro assump_15
        intro assump_16
        have assump_66 : (p5 → p5) := by
          intro assump_29
          exact assump_29
        let assump_28 := assump_8 assump_66
        let assump_32 := And.left assump_28
        apply False.elim assump_32
    case inr assump_5 =>
      cases assump_3
      case intro assump_38 assump_39 =>
        apply Or.inl
        intro assump_44
        intro assump_45
        intro assump_46
        have assump_67 : (p5 → p5) := by
          intro assump_59
          exact assump_59
        let assump_58 := assump_38 assump_67
        let assump_62 := And.left assump_58
        apply False.elim assump_62


variable (p3 p4 p6 p7 p1 p5 p0 : Prop)
theorem file47_86139 : (((((p3 ∧ p5) → (p4 → p7)) → False) ∨ (((p1 → p0) ∨ (True → False)) → ((p3 → False) → False))) → ((((p1 ∧ False) ∧ (False ∧ p6)) → False) ∨ (((p0 → False) ∨ (p4 ∧ p0)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
  case inr assump_3 =>
    apply Or.inl
    intro assump_17
    cases assump_17
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        apply False.elim assump_21


variable (p0 p1 p2 p6 p4 p7 : Prop)
theorem file47_86842 : (((((True ∧ True) → False) → ((p1 → False) ∧ (p0 ∧ p2))) ∨ (((False ∨ p6) → False) ∧ ((p0 → True) ∧ (p7 ∨ p1)))) → ((((p0 ∧ p1) ∨ (True → False)) → ((p4 → p7) → (p4 → p4))) ∨ (((False ∧ p7) → False) ∨ ((False ∧ p1) ∨ (p7 ∨ p1))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_6
    case inl assump_13 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        exact assump_8
    case inr assump_14 =>
      exact assump_8
  case inr assump_3 =>
    cases assump_3
    case intro assump_23 assump_24 =>
      cases assump_24
      case intro assump_27 assump_28 =>
        cases assump_28
        case inl assump_31 =>
          apply Or.inl
          intro assump_35
          intro assump_36
          intro assump_37
          cases assump_35
          case inl assump_42 =>
            cases assump_42
            case intro assump_44 assump_45 =>
              exact assump_37
          case inr assump_43 =>
            exact assump_37
        case inr assump_32 =>
          apply Or.inl
          intro assump_54
          intro assump_55
          intro assump_56
          cases assump_54
          case inl assump_61 =>
            cases assump_61
            case intro assump_63 assump_64 =>
              exact assump_56
          case inr assump_62 =>
            exact assump_56


variable (p0 p2 p5 p7 p1 p4 : Prop)
theorem file47_88319 : (((((p5 ∨ True) ∧ (p5 → False)) ∧ ((True → p5) ∨ (p7 ∧ p5))) ∧ (((p5 → p5) → False) ∧ ((p4 → p1) ∧ (True → False)))) → ((((p5 → p4) → (p7 → False)) → ((p2 → p7) → (True → p5))) ∧ (((True → False) → (p0 → True)) → ((p4 ∨ p5) → (p1 → p1))))) := by
  intro assump_29
  apply And.intro
  intro assump_30
  intro assump_31
  intro assump_32
  cases assump_29
  case intro assump_39 assump_40 =>
    cases assump_39
    case intro assump_41 assump_42 =>
      cases assump_41
      case intro assump_43 assump_44 =>
        cases assump_43
        case inl assump_45 =>
          cases assump_42
          case inl assump_51 =>
            cases assump_40
            case intro assump_55 assump_56 =>
              cases assump_56
              case intro assump_59 assump_60 =>
                exact assump_45
          case inr assump_52 =>
            cases assump_52
            case intro assump_65 assump_66 =>
              cases assump_40
              case intro assump_71 assump_72 =>
                cases assump_72
                case intro assump_75 assump_76 =>
                  exact assump_66
        case inr assump_46 =>
          cases assump_42
          case inl assump_85 =>
            cases assump_40
            case intro assump_89 assump_90 =>
              cases assump_90
              case intro assump_93 assump_94 =>
                have assump_286 : True := by
                  apply True.intro
                let assump_99 := assump_94 assump_286
                apply False.elim assump_99
          case inr assump_86 =>
            cases assump_86
            case intro assump_103 assump_104 =>
              cases assump_40
              case intro assump_109 assump_110 =>
                cases assump_110
                case intro assump_113 assump_114 =>
                  exact assump_104
  intro assump_119
  intro assump_120
  intro assump_121
  cases assump_120
  case inl assump_124 =>
    cases assump_29
    case intro assump_130 assump_131 =>
      cases assump_130
      case intro assump_132 assump_133 =>
        cases assump_132
        case intro assump_134 assump_135 =>
          cases assump_134
          case inl assump_136 =>
            cases assump_133
            case inl assump_142 =>
              cases assump_131
              case intro assump_146 assump_147 =>
                cases assump_147
                case intro assump_150 assump_151 =>
                  exact assump_121
            case inr assump_143 =>
              cases assump_143
              case intro assump_156 assump_157 =>
                cases assump_131
                case intro assump_162 assump_163 =>
                  cases assump_163
                  case intro assump_166 assump_167 =>
                    exact assump_121
          case inr assump_137 =>
            cases assump_133
            case inl assump_176 =>
              cases assump_131
              case intro assump_180 assump_181 =>
                cases assump_181
                case intro assump_184 assump_185 =>
                  exact assump_121
            case inr assump_177 =>
              cases assump_177
              case intro assump_190 assump_191 =>
                cases assump_131
                case intro assump_196 assump_197 =>
                  cases assump_197
                  case intro assump_200 assump_201 =>
                    exact assump_121
  case inr assump_125 =>
    cases assump_29
    case intro assump_210 assump_211 =>
      cases assump_210
      case intro assump_212 assump_213 =>
        cases assump_212
        case intro assump_214 assump_215 =>
          cases assump_214
          case inl assump_216 =>
            cases assump_213
            case inl assump_222 =>
              cases assump_211
              case intro assump_226 assump_227 =>
                cases assump_227
                case intro assump_230 assump_231 =>
                  exact assump_121
            case inr assump_223 =>
              cases assump_223
              case intro assump_236 assump_237 =>
                cases assump_211
                case intro assump_242 assump_243 =>
                  cases assump_243
                  case intro assump_246 assump_247 =>
                    exact assump_121
          case inr assump_217 =>
            cases assump_213
            case inl assump_256 =>
              cases assump_211
              case intro assump_260 assump_261 =>
                cases assump_261
                case intro assump_264 assump_265 =>
                  exact assump_121
            case inr assump_257 =>
              cases assump_257
              case intro assump_270 assump_271 =>
                cases assump_211
                case intro assump_276 assump_277 =>
                  cases assump_277
                  case intro assump_280 assump_281 =>
                    exact assump_121


variable (p4 : Prop)
theorem file47_93263 : ((((((p4 ∨ True) ∨ (False ∧ True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p4 ∨ True) ∨ (False ∧ True)) → False) → False) := by
    intro assump_5
    have assump_16 : ((p4 ∨ True) ∨ (False ∧ True)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p0 p4 p3 p2 p7 p1 : Prop)
theorem file47_93768 : ((((((p0 ∧ p5) ∧ (False ∨ p7)) → ((p0 ∧ p7) ∨ (p2 ∨ False))) ∨ (((p2 ∧ p4) → (p1 → p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p0 ∧ p5) ∧ (False ∨ p7)) → ((p0 ∧ p7) ∨ (p2 ∨ False))) ∨ (((p2 ∧ p4) → (p1 → p3)) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply False.elim assump_14
        case inr assump_15 =>
          apply Or.inl
          apply And.intro
          exact assump_8
          exact assump_15
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p5 p7 p6 p2 : Prop)
theorem file47_94517 : ((((((p5 → p2) → (False ∨ p5)) → False) → False) ∧ ((((p5 → p5) → (p5 → False)) → False) ∧ (((True ∧ p7) ∨ (p6 → False)) ∧ ((False → False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            have assump_40 : (False → False) := by
              intro assump_23
              apply False.elim assump_23
            let assump_22 := assump_11 assump_40
            apply False.elim assump_22
        case inr assump_13 =>
          have assump_41 : (False → False) := by
            intro assump_34
            apply False.elim assump_34
          let assump_33 := assump_11 assump_41
          apply False.elim assump_33


variable (p0 p7 p2 p6 p4 p3 : Prop)
theorem file47_95492 : (((((p2 ∧ False) → (p7 ∨ p6)) ∨ ((p7 → p4) ∨ (False ∨ False))) → (((False ∧ p6) → (p7 → False)) ∧ ((False ∧ True) → False))) ∨ ((((p0 ∧ p2) ∨ (p6 ∧ False)) ∧ ((p7 → p2) ∨ (p6 ∨ p2))) → (((p6 ∧ p6) ∧ (p3 ∧ p0)) ∨ ((True → False) → False)))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    apply False.elim assump_6
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    apply False.elim assump_11


variable (p4 p0 p5 p7 p3 : Prop)
theorem file47_96063 : ((((((False ∧ p7) → False) → False) → (((False ∧ p3) → False) ∨ ((p7 ∨ p5) → (p4 ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((False ∧ p7) → False) → False) → (((False ∧ p3) → False) ∨ ((p7 ∨ p5) → (p4 ∨ p0)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p2 p4 : Prop)
theorem file47_96563 : ((((((p4 ∧ p2) → (True ∨ False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p4 ∧ p2) → (True ∨ False)) → False) → False) := by
    intro assump_5
    have assump_23 : ((p4 ∧ p2) → (True ∨ False)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply True.intro
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p3 p5 p4 : Prop)
theorem file47_97120 : ((((((p2 ∧ p4) → (p4 ∧ True)) ∨ ((p3 ∨ p2) → False)) ∨ (((True ∧ p4) ∨ (p5 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p2 ∧ p4) → (p4 ∧ True)) ∨ ((p3 ∨ p2) → False)) ∨ (((True ∧ p4) ∨ (p5 → False)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      exact assump_7
    apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p6 p1 p0 p3 : Prop)
theorem file47_97666 : (((((p7 ∧ p1) → (p6 ∨ p1)) ∨ ((p6 ∨ p6) → (False ∨ p1))) → (((p6 → False) → False) → False)) → ((((p0 → p3) → (p7 ∧ p0)) → ((p7 → False) → False)) → (((p6 ∧ p1) ∧ (p7 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      have assump_37 : (((p7 ∧ p1) → (p6 ∨ p1)) ∨ ((p6 ∨ p6) → (False ∨ p1))) := by
        apply Or.inl
        intro assump_19
        cases assump_19
        case intro assump_20 assump_21 =>
          apply Or.inl
          exact assump_6
      let assump_18 := assump_1 assump_37
      have assump_38 : ((p6 → False) → False) := by
        intro assump_27
        have assump_39 : p6 := by
          exact assump_6
        let assump_30 := assump_27 assump_39
        apply False.elim assump_30
      let assump_26 := assump_18 assump_38
      apply False.elim assump_26


variable (p0 p5 p1 p7 p6 : Prop)
theorem file47_98650 : ((((((p0 ∧ p5) → (p1 → False)) → ((False ∧ p6) → (p1 → p7))) ∨ (((p1 → False) ∨ (False ∨ False)) → ((p6 ∨ False) ∧ (p1 → p5)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p0 ∧ p5) → (p1 → False)) → ((False ∧ p6) → (p1 → p7))) ∨ (((p1 → False) ∨ (False ∨ False)) → ((p6 ∨ False) ∧ (p1 → p5)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p4 p1 p7 p6 p5 p0 : Prop)
theorem file47_99259 : (((((p0 ∨ p6) ∧ (p7 ∧ False)) → ((p0 ∨ p0) ∧ (p1 → False))) ∧ (((False → p6) → (False → p1)) → False)) → ((((p5 ∧ p7) → (p5 → False)) → False) ∧ (((True → False) ∨ (True ∨ p4)) → ((False → False) ∨ (p6 ∨ p7))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_57 : ((False → p6) → (False → p1)) := by
      intro assump_12
      intro assump_13
      apply False.elim assump_13
    let assump_11 := assump_6 assump_57
    apply False.elim assump_11
  intro assump_19
  cases assump_19
  case inl assump_20 =>
    cases assump_1
    case intro assump_24 assump_25 =>
      apply Or.inl
      intro assump_30
      apply False.elim assump_30
  case inr assump_21 =>
    cases assump_21
    case inl assump_33 =>
      cases assump_1
      case intro assump_37 assump_38 =>
        apply Or.inl
        intro assump_43
        apply False.elim assump_43
    case inr assump_34 =>
      cases assump_1
      case intro assump_48 assump_49 =>
        apply Or.inl
        intro assump_54
        apply False.elim assump_54


variable (p6 p0 p5 p7 p2 : Prop)
theorem file47_100411 : (((((False ∨ True) → False) → False) → False) → ((((p5 ∧ p5) → (p2 → p2)) ∨ ((p0 ∧ True) ∧ (p7 → False))) ∧ (((p0 ∧ p6) → False) → False))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    exact assump_5
  intro assump_14
  have assump_30 : (((False ∨ True) → False) → False) := by
    intro assump_20
    have assump_31 : (False ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_23 := assump_20 assump_31
    apply False.elim assump_23
  let assump_19 := assump_1 assump_30
  apply False.elim assump_19


variable (p5 p1 p3 p2 p6 : Prop)
theorem file47_101089 : (((((p2 ∨ True) ∨ (p6 → False)) → False) ∧ (((p5 ∧ True) → False) ∧ ((p3 → p6) ∧ (p1 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_23 : ((p2 ∨ True) ∨ (p6 → False)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_19 := assump_2 assump_23
        apply False.elim assump_19


variable (p1 p0 p3 p6 p4 p5 : Prop)
theorem file47_101657 : ((((((p0 ∨ p5) ∨ (p1 ∨ p1)) ∨ ((True ∧ p0) ∨ (p0 → False))) ∧ (((True ∨ p3) → False) ∧ ((p3 → False) ∧ (p1 ∧ p6)))) ∧ ((((p3 → False) → (p4 → p6)) ∨ ((p3 → False) → False)) → False)) → False) := by
  intro assump_33
  cases assump_33
  case intro assump_34 assump_35 =>
    cases assump_34
    case intro assump_36 assump_37 =>
      cases assump_36
      case inl assump_38 =>
        cases assump_38
        case inl assump_40 =>
          cases assump_40
          case inl assump_42 =>
            cases assump_37
            case intro assump_46 assump_47 =>
              cases assump_47
              case intro assump_50 assump_51 =>
                cases assump_51
                case intro assump_54 assump_55 =>
                  have assump_220 : (((p3 → False) → (p4 → p6)) ∨ ((p3 → False) → False)) := by
                    apply Or.inl
                    intro assump_63
                    intro assump_64
                    exact assump_55
                  let assump_62 := assump_35 assump_220
                  apply False.elim assump_62
          case inr assump_43 =>
            cases assump_37
            case intro assump_74 assump_75 =>
              cases assump_75
              case intro assump_78 assump_79 =>
                cases assump_79
                case intro assump_82 assump_83 =>
                  have assump_221 : (((p3 → False) → (p4 → p6)) ∨ ((p3 → False) → False)) := by
                    apply Or.inl
                    intro assump_91
                    intro assump_92
                    exact assump_83
                  let assump_90 := assump_35 assump_221
                  apply False.elim assump_90
        case inr assump_41 =>
          cases assump_41
          case inl assump_100 =>
            cases assump_37
            case intro assump_104 assump_105 =>
              cases assump_105
              case intro assump_108 assump_109 =>
                cases assump_109
                case intro assump_112 assump_113 =>
                  have assump_222 : (((p3 → False) → (p4 → p6)) ∨ ((p3 → False) → False)) := by
                    apply Or.inl
                    intro assump_121
                    intro assump_122
                    exact assump_113
                  let assump_120 := assump_35 assump_222
                  apply False.elim assump_120
          case inr assump_101 =>
            cases assump_37
            case intro assump_132 assump_133 =>
              cases assump_133
              case intro assump_136 assump_137 =>
                cases assump_137
                case intro assump_140 assump_141 =>
                  have assump_223 : (((p3 → False) → (p4 → p6)) ∨ ((p3 → False) → False)) := by
                    apply Or.inl
                    intro assump_149
                    intro assump_150
                    exact assump_141
                  let assump_148 := assump_35 assump_223
                  apply False.elim assump_148
      case inr assump_39 =>
        cases assump_39
        case inl assump_158 =>
          cases assump_158
          case intro assump_160 assump_161 =>
            cases assump_37
            case intro assump_166 assump_167 =>
              cases assump_167
              case intro assump_170 assump_171 =>
                cases assump_171
                case intro assump_174 assump_175 =>
                  have assump_224 : (((p3 → False) → (p4 → p6)) ∨ ((p3 → False) → False)) := by
                    apply Or.inl
                    intro assump_183
                    intro assump_184
                    exact assump_175
                  let assump_182 := assump_35 assump_224
                  apply False.elim assump_182
        case inr assump_159 =>
          cases assump_37
          case intro assump_194 assump_195 =>
            cases assump_195
            case intro assump_198 assump_199 =>
              cases assump_199
              case intro assump_202 assump_203 =>
                have assump_225 : (((p3 → False) → (p4 → p6)) ∨ ((p3 → False) → False)) := by
                  apply Or.inl
                  intro assump_211
                  intro assump_212
                  exact assump_203
                let assump_210 := assump_35 assump_225
                apply False.elim assump_210


