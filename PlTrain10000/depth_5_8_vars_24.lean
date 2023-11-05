variable (p1 p3 p0 p2 p5 p4 p7 : Prop)
theorem file24_47 : (((((False ∧ True) ∧ (p3 → p1)) ∧ ((p4 → p5) → False)) ∧ (((p1 → False) → False) → False)) → ((((p4 ∨ p1) ∧ (False ∨ p1)) → ((p5 ∧ p1) → False)) → (((p0 ∨ p3) → (p3 ∨ p2)) ∧ ((p7 ∨ p7) → (p0 ∨ p3))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
  case inr assump_5 =>
    cases assump_1
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          cases assump_28
          case intro assump_30 assump_31 =>
            apply False.elim assump_30
  intro assump_34
  cases assump_34
  case inl assump_35 =>
    cases assump_1
    case intro assump_41 assump_42 =>
      cases assump_41
      case intro assump_43 assump_44 =>
        cases assump_43
        case intro assump_45 assump_46 =>
          cases assump_45
          case intro assump_47 assump_48 =>
            apply False.elim assump_47
  case inr assump_36 =>
    cases assump_1
    case intro assump_55 assump_56 =>
      cases assump_55
      case intro assump_57 assump_58 =>
        cases assump_57
        case intro assump_59 assump_60 =>
          cases assump_59
          case intro assump_61 assump_62 =>
            apply False.elim assump_61


variable (p6 p7 p1 p4 p0 p5 p3 : Prop)
theorem file24_1709 : ((((((p3 → p7) ∨ (p5 → False)) → ((True ∧ p6) ∨ (p1 ∧ p3))) ∧ (((p3 ∧ p0) → False) ∧ ((p7 → False) → (p7 → False)))) ∧ ((((True → False) → (p4 → False)) ∨ ((p6 ∧ p4) ∧ (True ∨ p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_30 : (((True → False) → (p4 → False)) ∨ ((p6 ∧ p4) ∧ (True ∨ p4))) := by
          apply Or.inl
          intro assump_17
          intro assump_18
          have assump_31 : True := by
            apply True.intro
          let assump_23 := assump_17 assump_31
          apply False.elim assump_23
        let assump_16 := assump_3 assump_30
        apply False.elim assump_16


variable (p3 p2 p6 p0 p1 p4 : Prop)
theorem file24_2556 : ((((((True → False) → False) ∨ ((p2 → False) → (p3 ∨ p6))) ∨ (((p4 ∨ p2) ∧ (p1 ∧ p3)) → ((p3 ∧ p0) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True → False) → False) ∨ ((p2 → False) → (p3 ∨ p6))) ∨ (((p4 ∨ p2) ∧ (p1 ∧ p3)) → ((p3 ∧ p0) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p6 p2 p7 p0 p4 p3 : Prop)
theorem file24_3145 : (((((True → False) ∧ (p3 → p4)) ∧ ((p0 ∨ p1) → (True ∧ p2))) → (((False ∧ p4) ∧ (False → False)) ∧ ((False ∧ p6) → False))) ∨ ((((p7 → False) ∨ (p4 → p0)) ∧ ((False ∨ p0) → (p2 ∨ p2))) ∧ (((p2 → p3) → (p1 ∧ p2)) ∧ ((p3 ∧ p4) ∧ (False → False))))) := by
  apply Or.inl
  intro assump_11
  apply And.intro
  apply And.intro
  apply And.intro
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      have assump_52 : True := by
        apply True.intro
      let assump_24 := assump_14 assump_52
      apply False.elim assump_24
  cases assump_11
  case intro assump_28 assump_29 =>
    cases assump_28
    case intro assump_30 assump_31 =>
      have assump_53 : True := by
        apply True.intro
      let assump_40 := assump_30 assump_53
      apply False.elim assump_40
  intro assump_44
  apply False.elim assump_44
  intro assump_47
  cases assump_47
  case intro assump_48 assump_49 =>
    apply False.elim assump_48


variable (p4 p1 p3 p0 p6 p2 p7 : Prop)
theorem file24_4192 : (((((p7 ∨ p4) ∧ (p4 → False)) → ((p7 → p0) ∨ (p2 → False))) → (((False → True) ∧ (False → p6)) ∨ ((p7 ∨ p3) ∨ (p2 → p1)))) ∨ ((((True ∨ p6) → False) → False) ∧ (((p2 ∧ p7) ∨ (p6 → False)) ∨ ((p3 → False) → (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  apply True.intro
  intro assump_5
  apply False.elim assump_5


variable (p2 p5 p3 p1 p7 p0 : Prop)
theorem file24_4627 : (((((p7 ∨ p5) ∨ (p2 ∨ p0)) → False) ∧ (((p1 → False) ∨ (p5 → True)) ∧ ((False → False) → (True → False)))) → ((((p3 ∨ p2) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        have assump_37 : (False → False) := by
          intro assump_18
          apply False.elim assump_18
        let assump_17 := assump_10 assump_37
        have assump_38 : True := by
          apply True.intro
        let assump_21 := assump_17 assump_38
        apply False.elim assump_21
      case inr assump_12 =>
        have assump_39 : (False → False) := by
          intro assump_30
          apply False.elim assump_30
        let assump_29 := assump_10 assump_39
        have assump_40 : True := by
          apply True.intro
        let assump_33 := assump_29 assump_40
        apply False.elim assump_33


variable (p7 p5 p6 p1 p0 p2 p3 p4 : Prop)
theorem file24_5663 : (((((p6 ∧ False) → (p6 ∨ p2)) ∨ ((p7 ∨ p0) ∧ (p1 ∧ p0))) → False) → ((((True ∨ p6) ∧ (False → False)) → False) → (((p4 ∨ False) → (p0 → p7)) → ((p7 ∧ p3) ∨ (False → p5))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply Or.inr
  intro assump_10
  apply False.elim assump_10


variable (p5 p1 : Prop)
theorem file24_6003 : ((((((False → p1) → False) → False) ∨ (((False → False) ∨ (p5 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → p1) → False) → False) ∨ (((False → False) ∨ (p5 → False)) → False)) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (False → p1) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p6 p0 p5 p3 : Prop)
theorem file24_6551 : (((((p7 ∧ p0) ∨ (p5 ∨ False)) → ((False → False) ∧ (p6 ∨ p6))) ∧ (((p7 ∧ False) → (p3 → False)) → False)) → ((((False → False) ∧ (p6 ∨ p3)) → False) → False)) := by
  intro assump_13
  intro assump_14
  cases assump_13
  case intro assump_17 assump_18 =>
    have assump_37 : ((p7 ∧ False) → (p3 → False)) := by
      intro assump_24
      intro assump_25
      cases assump_24
      case intro assump_28 assump_29 =>
        apply False.elim assump_29
    let assump_23 := assump_18 assump_37
    apply False.elim assump_23


variable (p2 p1 p0 p7 p3 p6 p4 p5 : Prop)
theorem file24_7142 : ((((((p4 ∨ p5) ∨ (p2 → False)) → ((p7 ∧ p7) ∨ (p3 → False))) ∧ (((p6 → p1) → False) ∧ ((p6 ∧ p7) ∧ (p4 ∨ False)))) ∧ ((((p4 ∨ True) → (p4 ∧ False)) ∨ ((False → True) ∨ (p0 → False))) ∧ (((False → False) ∧ (False ∨ True)) → False))) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_18
      case intro assump_21 assump_22 =>
        cases assump_22
        case intro assump_25 assump_26 =>
          cases assump_25
          case intro assump_27 assump_28 =>
            cases assump_26
            case inl assump_33 =>
              cases assump_16
              case intro assump_37 assump_38 =>
                cases assump_37
                case inl assump_39 =>
                  have assump_78 : ((False → False) ∧ (False ∨ True)) := by
                    apply And.intro
                    intro assump_46
                    apply False.elim assump_46
                    apply Or.inr
                    apply True.intro
                  let assump_45 := assump_38 assump_78
                  apply False.elim assump_45
                case inr assump_40 =>
                  cases assump_40
                  case inl assump_52 =>
                    have assump_79 : ((False → False) ∧ (False ∨ True)) := by
                      apply And.intro
                      intro assump_59
                      apply False.elim assump_59
                      apply Or.inr
                      apply True.intro
                    let assump_58 := assump_38 assump_79
                    apply False.elim assump_58
                  case inr assump_53 =>
                    have assump_80 : ((False → False) ∧ (False ∨ True)) := by
                      apply And.intro
                      intro assump_70
                      apply False.elim assump_70
                      apply Or.inr
                      apply True.intro
                    let assump_69 := assump_38 assump_80
                    apply False.elim assump_69
            case inr assump_34 =>
              apply False.elim assump_34


variable (p5 p2 p0 : Prop)
theorem file24_9332 : (((((p2 ∨ True) ∨ (p5 → True)) ∨ ((p0 → False) ∧ (p0 → False))) → False) → False) := by
  intro assump_1
  have assump_8 : (((p2 ∨ True) ∨ (p5 → True)) ∨ ((p0 → False) ∧ (p0 → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p4 p0 p2 p7 p6 : Prop)
theorem file24_9716 : (((((p6 ∧ p6) ∨ (p2 → p7)) ∨ ((p4 ∨ p4) ∨ (p6 → p4))) ∧ (((False → False) ∨ (False ∧ p0)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          have assump_71 : ((False → False) ∨ (False ∧ p0)) := by
            apply Or.inl
            intro assump_17
            apply False.elim assump_17
          let assump_16 := assump_3 assump_71
          apply False.elim assump_16
      case inr assump_7 =>
        have assump_72 : ((False → False) ∨ (False ∧ p0)) := by
          apply Or.inl
          intro assump_28
          apply False.elim assump_28
        let assump_27 := assump_3 assump_72
        apply False.elim assump_27
    case inr assump_5 =>
      cases assump_5
      case inl assump_34 =>
        cases assump_34
        case inl assump_36 =>
          have assump_73 : ((False → False) ∨ (False ∧ p0)) := by
            apply Or.inl
            intro assump_43
            apply False.elim assump_43
          let assump_42 := assump_3 assump_73
          apply False.elim assump_42
        case inr assump_37 =>
          have assump_74 : ((False → False) ∨ (False ∧ p0)) := by
            apply Or.inl
            intro assump_54
            apply False.elim assump_54
          let assump_53 := assump_3 assump_74
          apply False.elim assump_53
      case inr assump_35 =>
        have assump_75 : ((False → False) ∨ (False ∧ p0)) := by
          apply Or.inl
          intro assump_65
          apply False.elim assump_65
        let assump_64 := assump_3 assump_75
        apply False.elim assump_64


variable (p2 p3 p0 p1 p6 p7 p5 : Prop)
theorem file24_11511 : (((((p6 → False) ∧ (True → False)) → False) ∨ (((p3 ∧ True) ∧ (False → False)) → False)) → ((((p0 ∧ p1) ∨ (p1 ∧ p3)) → False) → (((p0 ∨ p5) ∨ (False → p2)) ∨ ((p3 ∨ p7) → False)))) := by
  intro assump_5
  intro assump_6
  cases assump_5
  case inl assump_9 =>
    apply Or.inl
    apply Or.inr
    intro assump_13
    apply False.elim assump_13
  case inr assump_10 =>
    apply Or.inl
    apply Or.inr
    intro assump_18
    apply False.elim assump_18


variable (p2 p1 p6 p3 p0 : Prop)
theorem file24_12023 : ((((((p3 → False) ∧ (p3 → p3)) → ((p6 ∧ p3) → False)) ∨ (((p0 → False) → (False ∨ p6)) ∧ ((p2 → False) ∧ (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((p3 → False) ∧ (p3 → p3)) → ((p6 ∧ p3) → False)) ∨ (((p0 → False) → (False ∨ p6)) ∧ ((p2 → False) ∧ (p1 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        have assump_29 : p3 := by
          exact assump_8
        let assump_21 := assump_13 assump_29
        apply False.elim assump_21
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p5 p3 : Prop)
theorem file24_12752 : ((((((False ∨ p5) ∧ (p5 → False)) ∨ ((False ∧ p3) → False)) ∨ (((True ∧ True) ∧ (True → p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∨ p5) ∧ (p5 → False)) ∨ ((False ∧ p3) → False)) ∨ (((True ∧ True) ∧ (True → p3)) → False)) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p7 p5 p6 p3 : Prop)
theorem file24_13281 : (((((False → True) ∧ (p5 ∨ True)) → ((False → p5) ∧ (True ∨ False))) → False) → ((((p3 ∨ p6) ∧ (p7 → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_25 : (((False → True) ∧ (p5 ∨ True)) → ((False → p5) ∧ (True ∨ False))) := by
    intro assump_8
    apply And.intro
    intro assump_9
    apply False.elim assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      cases assump_13
      case inl assump_16 =>
        apply Or.inl
        apply True.intro
      case inr assump_17 =>
        apply Or.inl
        apply True.intro
  let assump_7 := assump_1 assump_25
  apply False.elim assump_7


variable (p0 p6 p4 p1 p7 p5 : Prop)
theorem file24_13981 : (((((p6 ∨ p1) ∧ (True → False)) ∧ ((True ∨ p6) ∨ (True → False))) → (((False ∧ p5) → (p6 → False)) ∧ ((p0 ∧ p4) ∨ (p1 → False)))) ∨ ((((p7 → p4) → (p0 ∧ p4)) ∨ ((p6 → p7) ∨ (p5 → True))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    apply False.elim assump_6
  cases assump_1
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        cases assump_11
        case inl assump_20 =>
          cases assump_20
          case inl assump_22 =>
            apply Or.inr
            intro assump_26
            have assump_94 : True := by
              apply True.intro
            let assump_30 := assump_13 assump_94
            apply False.elim assump_30
          case inr assump_23 =>
            apply Or.inr
            intro assump_36
            have assump_95 : True := by
              apply True.intro
            let assump_41 := assump_13 assump_95
            apply False.elim assump_41
        case inr assump_21 =>
          apply Or.inr
          intro assump_47
          have assump_96 : True := by
            apply True.intro
          let assump_51 := assump_21 assump_96
          apply False.elim assump_51
      case inr assump_15 =>
        cases assump_11
        case inl assump_59 =>
          cases assump_59
          case inl assump_61 =>
            apply Or.inr
            intro assump_65
            have assump_97 : True := by
              apply True.intro
            let assump_69 := assump_13 assump_97
            apply False.elim assump_69
          case inr assump_62 =>
            apply Or.inr
            intro assump_75
            have assump_98 : True := by
              apply True.intro
            let assump_80 := assump_13 assump_98
            apply False.elim assump_80
        case inr assump_60 =>
          apply Or.inr
          intro assump_86
          have assump_99 : True := by
            apply True.intro
          let assump_90 := assump_60 assump_99
          apply False.elim assump_90


variable (p7 p6 p4 p1 p2 : Prop)
theorem file24_16191 : ((((((p4 ∧ p6) ∧ (p1 ∧ False)) ∨ ((False ∧ True) → (p1 → p2))) → (((p7 ∨ True) → False) → ((p1 → False) ∨ (p7 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_39 : ((((p4 ∧ p6) ∧ (p1 ∧ False)) ∨ ((False ∧ True) → (p1 → p2))) → (((p7 ∨ True) → False) → ((p1 → False) ∨ (p7 ∨ p6)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_12
          case intro assump_19 assump_20 =>
            apply False.elim assump_20
    case inr assump_10 =>
      apply Or.inl
      intro assump_27
      have assump_40 : (p7 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_32 := assump_6 assump_40
      apply False.elim assump_32
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p0 p2 p4 p6 p3 p5 p1 p7 : Prop)
theorem file24_17171 : (((((p4 ∨ p4) ∨ (p3 → p3)) ∨ ((True ∧ p2) ∧ (p7 ∧ p0))) → False) → ((((True → False) ∨ (p6 ∧ p5)) → False) ∨ (((p1 ∧ p1) → False) ∨ ((False → False) → False)))) := by
  intro assump_23
  apply Or.inl
  intro assump_26
  cases assump_26
  case inl assump_27 =>
    have assump_50 : True := by
      apply True.intro
    let assump_31 := assump_27 assump_50
    apply False.elim assump_31
  case inr assump_28 =>
    cases assump_28
    case intro assump_35 assump_36 =>
      have assump_51 : (((p4 ∨ p4) ∨ (p3 → p3)) ∨ ((True ∧ p2) ∧ (p7 ∧ p0))) := by
        apply Or.inl
        apply Or.inr
        intro assump_44
        exact assump_44
      let assump_43 := assump_23 assump_51
      apply False.elim assump_43


variable (p5 p4 p2 p1 p6 : Prop)
theorem file24_17946 : (((((p2 ∧ p5) ∨ (p1 ∨ False)) ∨ ((p1 ∧ p4) → (p6 ∨ p1))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p2 ∧ p5) ∨ (p1 ∨ False)) ∨ ((p1 ∧ p4) → (p6 ∨ p1))) := by
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      exact assump_6
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p7 p2 p1 p3 p0 p4 : Prop)
theorem file24_18383 : (((((p3 → True) ∨ (p1 → False)) → False) → (((p5 ∨ p4) ∧ (p3 → False)) ∨ ((p5 ∧ p4) ∨ (True → p0)))) ∨ ((((p4 ∨ p0) → (p0 ∨ p5)) ∧ ((p2 → False) → False)) → (((p7 → False) → False) ∧ ((True ∧ True) ∧ (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply Or.inr
  intro assump_4
  have assump_12 : ((p3 → True) ∨ (p1 → False)) := by
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_7 := assump_1 assump_12
  apply False.elim assump_7


variable (p6 p5 p7 p1 p3 p2 p0 : Prop)
theorem file24_18924 : ((((((p0 → False) ∨ (True ∨ p5)) → ((False ∨ p2) → (p5 → p1))) → (((p7 ∨ p6) ∨ (p7 → False)) → False)) ∧ ((((False → False) ∧ (False → p3)) → ((False → False) ∧ (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((False → False) ∧ (False → p3)) → ((False → False) ∧ (False → False))) := by
      intro assump_9
      apply And.intro
      intro assump_10
      apply False.elim assump_10
      intro assump_13
      apply False.elim assump_13
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p6 p3 p1 p5 : Prop)
theorem file24_19572 : ((((((p6 ∧ p1) → (True → p3)) → ((p3 ∧ p5) ∧ (p1 ∧ p6))) → False) ∧ ((((p1 → False) ∧ (p1 → False)) → ((True ∨ p6) ∧ (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((p1 → False) ∧ (p1 → False)) → ((True ∨ p6) ∧ (False → False))) := by
      intro assump_9
      apply And.intro
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply True.intro
      intro assump_16
      apply False.elim assump_16
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p3 p4 p1 p2 p5 p6 p7 : Prop)
theorem file24_20230 : ((((((False ∧ p3) → (p1 → False)) → ((p3 ∨ p2) → (p6 ∧ p2))) ∨ (((p4 → p1) ∨ (True ∨ True)) → False)) ∧ ((((p1 ∨ True) → (p2 → True)) ∨ ((p5 ∨ p3) ∧ (p6 ∨ p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_26 : (((p1 ∨ True) → (p2 → True)) ∨ ((p5 ∨ p3) ∧ (p6 ∨ p7))) := by
        apply Or.inl
        intro assump_11
        intro assump_12
        apply True.intro
      let assump_10 := assump_3 assump_26
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_27 : (((p1 ∨ True) → (p2 → True)) ∨ ((p5 ∨ p3) ∧ (p6 ∨ p7))) := by
        apply Or.inl
        intro assump_21
        intro assump_22
        apply True.intro
      let assump_20 := assump_3 assump_27
      apply False.elim assump_20


variable (p2 p4 p5 p7 p1 : Prop)
theorem file24_21118 : (((((p2 → p1) ∧ (True → False)) → ((p4 → False) ∨ (p7 ∧ p4))) → (((p2 ∨ p4) ∧ (p5 ∧ False)) → False)) ∨ ((((p5 → False) ∨ (p5 ∨ p4)) → ((p4 ∧ p7) ∨ (True ∧ True))) → False)) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      cases assump_8
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
    case inr assump_10 =>
      cases assump_8
      case intro assump_21 assump_22 =>
        apply False.elim assump_22


variable (p7 p1 p4 p5 p0 : Prop)
theorem file24_21717 : (((((p1 ∧ p4) ∨ (p4 → False)) ∧ ((p1 ∨ p7) ∨ (p0 → False))) ∨ (((p7 → p4) ∨ (p5 ∨ True)) ∧ ((p0 → False) ∨ (True → p0)))) → ((((True → p4) ∨ (False ∨ p7)) → ((p4 ∧ True) → False)) → (((False → False) ∨ (p7 → p1)) ∨ ((True → False) ∨ (p4 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_8
          case inl assump_17 =>
            cases assump_17
            case inl assump_19 =>
              apply Or.inl
              apply Or.inl
              intro assump_23
              apply False.elim assump_23
            case inr assump_20 =>
              apply Or.inl
              apply Or.inl
              intro assump_28
              apply False.elim assump_28
          case inr assump_18 =>
            apply Or.inl
            apply Or.inl
            intro assump_33
            apply False.elim assump_33
      case inr assump_10 =>
        cases assump_8
        case inl assump_38 =>
          cases assump_38
          case inl assump_40 =>
            apply Or.inl
            apply Or.inl
            intro assump_44
            apply False.elim assump_44
          case inr assump_41 =>
            apply Or.inl
            apply Or.inl
            intro assump_49
            apply False.elim assump_49
        case inr assump_39 =>
          apply Or.inl
          apply Or.inl
          intro assump_54
          apply False.elim assump_54
  case inr assump_6 =>
    cases assump_6
    case intro assump_57 assump_58 =>
      cases assump_57
      case inl assump_59 =>
        cases assump_58
        case inl assump_63 =>
          apply Or.inl
          apply Or.inl
          intro assump_67
          apply False.elim assump_67
        case inr assump_64 =>
          apply Or.inl
          apply Or.inl
          intro assump_72
          apply False.elim assump_72
      case inr assump_60 =>
        cases assump_60
        case inl assump_75 =>
          cases assump_58
          case inl assump_79 =>
            apply Or.inl
            apply Or.inl
            intro assump_83
            apply False.elim assump_83
          case inr assump_80 =>
            apply Or.inl
            apply Or.inl
            intro assump_88
            apply False.elim assump_88
        case inr assump_76 =>
          cases assump_58
          case inl assump_93 =>
            apply Or.inl
            apply Or.inl
            intro assump_97
            apply False.elim assump_97
          case inr assump_94 =>
            apply Or.inl
            apply Or.inl
            intro assump_102
            apply False.elim assump_102


variable (p2 p7 p4 p3 p6 : Prop)
theorem file24_24562 : ((((((p6 → False) → (p2 → False)) → False) → False) ∧ ((((p2 ∧ p3) → False) → ((p4 → False) ∨ (p3 ∨ p6))) ∧ (((p7 → p7) ∨ (True → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_19 : ((p7 → p7) ∨ (True → False)) := by
        apply Or.inl
        intro assump_13
        exact assump_13
      let assump_12 := assump_7 assump_19
      apply False.elim assump_12


variable (p4 p3 p5 p0 p1 p2 : Prop)
theorem file24_25111 : (((((p5 ∨ p3) ∨ (p3 → False)) → False) → False) ∨ ((((p0 ∧ p2) → False) → False) ∧ (((True ∧ p1) ∧ (p4 ∧ p3)) ∨ ((False → False) ∧ (p5 → False))))) := by
  apply Or.inl
  intro assump_5
  have assump_20 : ((p5 ∨ p3) ∨ (p3 → False)) := by
    apply Or.inr
    intro assump_9
    have assump_21 : ((p5 ∨ p3) ∨ (p3 → False)) := by
      apply Or.inl
      apply Or.inr
      exact assump_9
    let assump_13 := assump_5 assump_21
    apply False.elim assump_13
  let assump_8 := assump_5 assump_20
  apply False.elim assump_8


variable (p4 p5 p7 p0 p2 p6 p3 p1 : Prop)
theorem file24_25700 : (((((p2 ∧ True) → (False → False)) ∨ ((p0 ∧ p1) ∧ (p6 → False))) → (((p1 ∧ p0) → (p7 → p5)) ∧ ((p3 → True) → (p7 → p6)))) → ((((True → False) ∨ (p7 ∧ p6)) → ((p7 → False) → (p7 ∧ p4))) ∨ (((p6 → p4) → (p3 → p3)) → ((p3 → False) ∨ (p3 → p6))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply And.intro
  cases assump_4
  case inl assump_8 =>
    have assump_44 : True := by
      apply True.intro
    let assump_12 := assump_8 assump_44
    apply False.elim assump_12
  case inr assump_9 =>
    cases assump_9
    case intro assump_16 assump_17 =>
      exact assump_16
  cases assump_4
  case inl assump_24 =>
    have assump_45 : True := by
      apply True.intro
    let assump_28 := assump_24 assump_45
    apply False.elim assump_28
  case inr assump_25 =>
    cases assump_25
    case intro assump_32 assump_33 =>
      have assump_46 : p7 := by
        exact assump_32
      let assump_40 := assump_5 assump_46
      apply False.elim assump_40


variable (p4 p2 p5 p6 p0 p3 : Prop)
theorem file24_26743 : ((((((p5 → False) → (p4 → p6)) ∧ ((p2 ∨ p0) ∨ (p3 → False))) → False) ∧ ((((p2 → False) → (False → p0)) ∨ ((p3 ∨ p3) ∨ (False → p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((p2 → False) → (False → p0)) ∨ ((p3 ∨ p3) ∨ (False → p5))) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p2 p6 p1 p0 p3 p5 : Prop)
theorem file24_27282 : (((((True → False) → (p6 ∨ p5)) → ((p2 ∨ True) → (p3 ∧ False))) → False) ∨ ((((p6 → False) ∧ (p3 ∨ True)) → ((p2 → False) → False)) ∧ (((p1 ∧ p0) → (True → False)) ∨ ((p5 → False) ∨ (False ∧ p5))))) := by
  apply Or.inl
  intro assump_1
  have assump_18 : ((True → False) → (p6 ∨ p5)) := by
    intro assump_5
    have assump_19 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  have assump_20 : (p2 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_12 := assump_4 assump_20
  let assump_13 := And.right assump_12
  apply False.elim assump_13


variable (p5 p4 p2 p3 p6 p1 p7 : Prop)
theorem file24_27997 : ((((((p4 → False) ∨ (p1 → p7)) → False) → (((p4 → p1) → (p1 → p3)) → False)) ∧ ((((p1 ∨ p2) → False) ∧ ((p1 → p3) ∧ (p2 ∧ p1))) ∧ (((False → p2) → (p4 → p6)) ∧ ((p5 ∧ p6) ∧ (p2 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_7
            case intro assump_22 assump_23 =>
              cases assump_23
              case intro assump_26 assump_27 =>
                cases assump_26
                case intro assump_28 assump_29 =>
                  have assump_40 : p2 := by
                    exact assump_16
                  let assump_36 := assump_27 assump_40
                  apply False.elim assump_36


variable (p2 p6 p0 p7 p5 p1 p3 p4 : Prop)
theorem file24_28998 : (((((p5 ∨ p7) → (p2 ∨ p7)) → ((p6 ∨ True) → (False → False))) → (((p1 ∧ p5) → (p6 → p6)) ∧ ((True ∨ p7) → (p1 → p7)))) → ((((p4 ∨ p4) → (p7 → True)) → False) → (((p0 → p3) ∨ (p1 → p2)) ∧ ((False → p5) ∧ (p7 ∨ p2))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply Or.inl
  intro assump_7
  have assump_50 : ((p4 ∨ p4) → (p7 → True)) := by
    intro assump_22
    intro assump_23
    apply True.intro
  let assump_21 := assump_2 assump_50
  apply False.elim assump_21
  apply And.intro
  intro assump_27
  apply False.elim assump_27
  have assump_51 : ((p4 ∨ p4) → (p7 → True)) := by
    intro assump_45
    intro assump_46
    apply True.intro
  let assump_44 := assump_2 assump_51
  apply False.elim assump_44


variable (p4 p7 p6 p2 p0 : Prop)
theorem file24_29785 : ((((((True ∨ p2) ∨ (p2 ∨ p0)) → False) → (((p4 → True) ∧ (False → p6)) ∧ ((p4 ∨ p6) → (p7 → True)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ p2) ∨ (p2 ∨ p0)) → False) → (((p4 → True) ∧ (False → p6)) ∧ ((p4 ∨ p6) → (p7 → True)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    intro assump_6
    apply True.intro
    intro assump_7
    apply False.elim assump_7
    intro assump_10
    intro assump_11
    apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p1 p5 p4 p0 p6 p2 : Prop)
theorem file24_30388 : (((((p6 ∧ p5) ∧ (True ∨ p2)) ∨ ((p3 ∨ p4) ∧ (p5 → p4))) ∨ (((p3 → False) ∧ (p2 ∧ False)) → False)) ∨ ((((p3 ∧ p0) → (False → p1)) → ((p0 ∧ p6) → (p4 → False))) ∨ (((p1 ∨ False) ∧ (p0 ∧ p0)) ∧ ((p0 → p5) → False)))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p4 p3 p1 p7 p2 p0 p6 : Prop)
theorem file24_30857 : ((((((p4 ∧ False) → (True → False)) → ((p0 ∧ p3) → (p6 → p6))) ∨ (((p1 → False) ∨ (p3 ∧ p7)) → ((p2 → True) → (p0 ∨ p7)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p4 ∧ False) → (True → False)) → ((p0 ∧ p3) → (p6 → p6))) ∨ (((p1 → False) ∨ (p3 ∧ p7)) → ((p2 → True) → (p0 ∨ p7)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      exact assump_7
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p4 p1 p6 p5 : Prop)
theorem file24_31438 : (((((True → False) ∧ (True → p6)) ∧ ((p1 ∧ p1) ∧ (p4 → p6))) ∧ (((p5 ∧ p5) → False) ∨ ((p6 → p6) ∧ (p5 → p5)))) → False) := by
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
            cases assump_3
            case inl assump_22 =>
              have assump_53 : True := by
                apply True.intro
              let assump_32 := assump_6 assump_53
              apply False.elim assump_32
            case inr assump_23 =>
              cases assump_23
              case intro assump_36 assump_37 =>
                have assump_54 : True := by
                  apply True.intro
                let assump_49 := assump_6 assump_54
                apply False.elim assump_49


variable (p4 p1 p3 p7 p5 p2 p0 : Prop)
theorem file24_32458 : (((((False ∧ p5) → False) → False) ∧ (((p7 ∨ p7) → (p7 → False)) ∧ ((p3 ∧ p0) → False))) → ((((p7 ∧ p1) → (p2 ∨ False)) ∧ ((p4 → False) → (p5 ∧ p4))) → (((p5 ∨ p1) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        have assump_33 : ((False ∧ p5) → False) := by
          intro assump_25
          cases assump_25
          case intro assump_26 assump_27 =>
            apply False.elim assump_26
        let assump_24 := assump_12 assump_33
        apply False.elim assump_24


variable (p4 p6 p0 p3 : Prop)
theorem file24_33192 : ((((((False → p0) ∨ (p0 ∧ True)) ∧ ((False ∧ p6) → False)) ∧ (((p4 → False) ∧ (False ∧ p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_25 : ((((False → p0) ∨ (p0 ∧ True)) ∧ ((False ∧ p6) → False)) ∧ (((p4 → False) ∧ (False ∧ p3)) → False)) := by
    apply And.intro
    apply And.intro
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      cases assump_15
      case intro assump_18 assump_19 =>
        apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p6 p5 p1 p2 p7 p4 p0 p3 : Prop)
theorem file24_33979 : (((((p5 ∨ p6) → (True ∨ p6)) → False) → (((p3 ∨ p3) ∧ (p3 → False)) → ((p4 → p4) → (p3 ∨ p7)))) ∨ ((((p1 ∧ p5) ∨ (p6 → True)) ∨ ((False ∨ p0) → (p3 → False))) ∧ (((p5 → False) ∧ (p2 → p1)) ∧ ((p1 → p3) → (p7 ∨ p7))))) := by
  apply Or.inl
  intro assump_25
  intro assump_26
  intro assump_27
  cases assump_26
  case intro assump_30 assump_31 =>
    cases assump_30
    case inl assump_32 =>
      apply Or.inl
      exact assump_32
    case inr assump_33 =>
      apply Or.inl
      exact assump_33


variable (p3 p5 p0 p7 p1 p4 : Prop)
theorem file24_34540 : ((((((p0 ∨ p1) ∧ (p3 → False)) → ((p7 → False) → (False → p0))) ∨ (((p5 → False) ∨ (p3 ∧ p4)) ∨ ((p1 → False) → (p1 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p0 ∨ p1) ∧ (p3 → False)) → ((p7 → False) → (False → p0))) ∨ (((p5 → False) ∨ (p3 ∧ p4)) ∨ ((p1 → False) → (p1 ∧ p4)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p5 p1 p2 p7 p4 p0 p3 p6 : Prop)
theorem file24_35089 : (((((p7 ∧ True) ∧ (p5 ∨ p2)) ∧ ((p2 ∧ p1) ∨ (p0 ∨ p4))) ∧ (((False → False) ∨ (p5 → False)) → ((p2 ∨ False) → False))) ∨ ((((p7 ∨ p3) → (p1 → False)) ∧ ((p6 ∧ True) → False)) → (((p0 ∨ p4) → (p6 → p7)) ∧ ((p6 → False) ∨ (p5 ∨ p3))))) := by
  apply Or.inr
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      have assump_46 : (p6 ∧ True) := by
        apply And.intro
        exact assump_3
        apply True.intro
      let assump_16 := assump_11 assump_46
      apply False.elim assump_16
  case inr assump_7 =>
    cases assump_1
    case intro assump_22 assump_23 =>
      have assump_47 : (p6 ∧ True) := by
        apply And.intro
        exact assump_3
        apply True.intro
      let assump_28 := assump_23 assump_47
      apply False.elim assump_28
  cases assump_1
  case intro assump_32 assump_33 =>
    apply Or.inl
    intro assump_38
    have assump_48 : (p6 ∧ True) := by
      apply And.intro
      exact assump_38
      apply True.intro
    let assump_42 := assump_33 assump_48
    apply False.elim assump_42


variable (p6 p0 p2 p7 p1 p5 p3 : Prop)
theorem file24_36299 : (((((p2 → p0) ∧ (p7 → p1)) → False) ∧ (((True → False) → False) → False)) → ((((p3 ∨ p7) → (p5 ∧ p6)) ∧ ((p1 → True) ∧ (p7 ∨ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          have assump_34 : ((True → False) → False) := by
            intro assump_22
            have assump_35 : True := by
              apply True.intro
            let assump_25 := assump_22 assump_35
            apply False.elim assump_25
          let assump_21 := assump_16 assump_34
          apply False.elim assump_21
      case inr assump_12 =>
        apply False.elim assump_12


variable (p0 p4 p6 p7 p1 p2 : Prop)
theorem file24_37155 : (((((p7 → p0) → False) ∧ ((p7 ∨ p4) ∧ (True → False))) → False) ∨ ((((p6 ∨ p0) → (p7 ∧ p1)) ∨ ((p6 ∨ True) ∧ (p2 → False))) ∨ (((False ∨ p4) → False) ∨ ((p2 → False) ∧ (p6 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_26 : True := by
          apply True.intro
        let assump_14 := assump_7 assump_26
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_27 : True := by
          apply True.intro
        let assump_22 := assump_7 assump_27
        apply False.elim assump_22


variable (p1 p3 p0 p6 p2 p7 : Prop)
theorem file24_37903 : ((((((p1 → p6) → False) ∨ ((True → False) → False)) → False) ∧ ((((False → False) ∧ (p1 → False)) ∨ ((p2 → p3) ∧ (p6 ∨ p7))) ∧ (((p0 → False) → (False → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_56 : ((p0 → False) → (False → False)) := by
            intro assump_19
            intro assump_20
            apply False.elim assump_20
          let assump_18 := assump_7 assump_56
          apply False.elim assump_18
      case inr assump_9 =>
        cases assump_9
        case intro assump_26 assump_27 =>
          cases assump_27
          case inl assump_30 =>
            have assump_57 : ((p0 → False) → (False → False)) := by
              intro assump_37
              intro assump_38
              apply False.elim assump_38
            let assump_36 := assump_7 assump_57
            apply False.elim assump_36
          case inr assump_31 =>
            have assump_58 : ((p0 → False) → (False → False)) := by
              intro assump_49
              intro assump_50
              apply False.elim assump_50
            let assump_48 := assump_7 assump_58
            apply False.elim assump_48


variable (p0 p6 p5 p7 : Prop)
theorem file24_39318 : ((((((p0 → p6) ∧ (p7 → p5)) → False) → (((False ∧ p6) → False) ∨ ((p0 ∧ p6) → (p0 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p0 → p6) ∧ (p7 → p5)) → False) → (((False ∧ p6) → False) ∨ ((p0 ∧ p6) → (p0 ∧ p0)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 p3 p0 p1 p7 p2 : Prop)
theorem file24_39832 : (((((p6 → True) → False) → False) ∨ (((False → False) → (p3 ∧ p7)) → False)) ∨ ((((p3 ∨ False) → (True → p7)) ∧ ((True ∨ p2) → (p3 ∨ True))) ∧ (((p0 ∧ p3) ∧ (p1 → False)) ∨ ((False ∨ p3) ∧ (p1 → True))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_9 : (p6 → True) := by
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p5 p7 p2 p0 p3 p1 : Prop)
theorem file24_40290 : (((((p1 → p3) ∧ (False ∧ True)) ∨ ((p3 → False) → (False ∧ p5))) ∧ (((False → False) → False) → False)) → ((((p2 → p7) ∧ (p7 ∧ False)) → False) ∨ (((p0 → p3) → False) ∨ ((p0 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
    case inr assump_5 =>
      apply Or.inl
      intro assump_18
      cases assump_18
      case intro assump_19 assump_20 =>
        cases assump_20
        case intro assump_23 assump_24 =>
          apply False.elim assump_24


variable (p1 p0 p5 p7 p4 p3 : Prop)
theorem file24_41055 : ((((((p5 ∧ p4) ∧ (p7 → False)) ∨ ((p5 ∨ p5) ∨ (True → p0))) → False) ∧ ((((p5 ∧ p7) ∨ (True → False)) ∧ ((False → p1) → False)) ∧ (((p0 → p3) → (True ∨ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            have assump_42 : ((p0 → p3) → (True ∨ True)) := by
              intro assump_23
              apply Or.inl
              apply True.intro
            let assump_22 := assump_7 assump_42
            apply False.elim assump_22
        case inr assump_11 =>
          have assump_43 : ((p0 → p3) → (True ∨ True)) := by
            intro assump_36
            apply Or.inl
            apply True.intro
          let assump_35 := assump_7 assump_43
          apply False.elim assump_35


variable (p3 p2 p1 p5 p6 p4 : Prop)
theorem file24_42099 : ((((((p6 ∨ p2) ∧ (p4 ∧ p5)) ∧ ((p6 ∨ p2) → (p1 ∨ p2))) ∨ (((False → False) ∨ (p3 ∧ p6)) ∨ ((p6 → False) → (p2 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p6 ∨ p2) ∧ (p4 ∧ p5)) ∧ ((p6 ∨ p2) → (p1 ∨ p2))) ∨ (((False → False) ∨ (p3 ∧ p6)) ∨ ((p6 → False) → (p2 ∨ False)))) := by
    apply Or.inr
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p6 p5 p0 p1 p4 p7 : Prop)
theorem file24_42635 : (((((p4 → p0) ∨ (p0 → p2)) ∨ ((p7 → False) ∧ (p0 ∨ p7))) ∨ (((p4 ∧ p4) ∨ (True ∧ p1)) → ((p1 → True) → False))) → ((((p4 ∨ False) ∧ (p5 ∨ p5)) ∧ ((p7 ∧ False) ∧ (p5 ∨ p2))) → (((p6 → False) → False) ∨ ((p5 → False) ∧ (p5 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_6
        case inl assump_11 =>
          cases assump_4
          case intro assump_15 assump_16 =>
            cases assump_15
            case intro assump_17 assump_18 =>
              apply False.elim assump_18
        case inr assump_12 =>
          cases assump_4
          case intro assump_25 assump_26 =>
            cases assump_25
            case intro assump_27 assump_28 =>
              apply False.elim assump_28
      case inr assump_8 =>
        apply False.elim assump_8


variable (p6 p1 p0 p2 p5 p7 p4 : Prop)
theorem file24_43638 : ((((((False → p6) ∧ (True → False)) → False) → False) ∨ ((((False ∨ p1) ∧ (True → False)) ∧ ((p7 ∨ p2) ∨ (p2 ∨ p5))) ∧ (((p0 ∨ p6) ∨ (p1 ∨ False)) ∨ ((p6 → False) ∨ (p4 → False))))) → False) := by
  intro assump_17
  cases assump_17
  case inl assump_18 =>
    have assump_273 : (((False → p6) ∧ (True → False)) → False) := by
      intro assump_23
      cases assump_23
      case intro assump_24 assump_25 =>
        have assump_274 : True := by
          apply True.intro
        let assump_30 := assump_25 assump_274
        apply False.elim assump_30
    let assump_22 := assump_18 assump_273
    apply False.elim assump_22
  case inr assump_19 =>
    cases assump_19
    case intro assump_37 assump_38 =>
      cases assump_37
      case intro assump_39 assump_40 =>
        cases assump_39
        case intro assump_41 assump_42 =>
          cases assump_41
          case inl assump_43 =>
            apply False.elim assump_43
          case inr assump_44 =>
            cases assump_40
            case inl assump_51 =>
              cases assump_51
              case inl assump_53 =>
                cases assump_38
                case inl assump_57 =>
                  cases assump_57
                  case inl assump_59 =>
                    cases assump_59
                    case inl assump_61 =>
                      have assump_275 : True := by
                        apply True.intro
                      let assump_67 := assump_42 assump_275
                      apply False.elim assump_67
                    case inr assump_62 =>
                      have assump_276 : True := by
                        apply True.intro
                      let assump_75 := assump_42 assump_276
                      apply False.elim assump_75
                  case inr assump_60 =>
                    cases assump_60
                    case inl assump_79 =>
                      have assump_277 : True := by
                        apply True.intro
                      let assump_85 := assump_42 assump_277
                      apply False.elim assump_85
                    case inr assump_80 =>
                      apply False.elim assump_80
                case inr assump_58 =>
                  cases assump_58
                  case inl assump_91 =>
                    have assump_278 : True := by
                      apply True.intro
                    let assump_97 := assump_42 assump_278
                    apply False.elim assump_97
                  case inr assump_92 =>
                    have assump_279 : True := by
                      apply True.intro
                    let assump_105 := assump_42 assump_279
                    apply False.elim assump_105
              case inr assump_54 =>
                cases assump_38
                case inl assump_111 =>
                  cases assump_111
                  case inl assump_113 =>
                    cases assump_113
                    case inl assump_115 =>
                      have assump_280 : True := by
                        apply True.intro
                      let assump_121 := assump_42 assump_280
                      apply False.elim assump_121
                    case inr assump_116 =>
                      have assump_281 : True := by
                        apply True.intro
                      let assump_129 := assump_42 assump_281
                      apply False.elim assump_129
                  case inr assump_114 =>
                    cases assump_114
                    case inl assump_133 =>
                      have assump_282 : True := by
                        apply True.intro
                      let assump_139 := assump_42 assump_282
                      apply False.elim assump_139
                    case inr assump_134 =>
                      apply False.elim assump_134
                case inr assump_112 =>
                  cases assump_112
                  case inl assump_145 =>
                    have assump_283 : True := by
                      apply True.intro
                    let assump_151 := assump_42 assump_283
                    apply False.elim assump_151
                  case inr assump_146 =>
                    have assump_284 : True := by
                      apply True.intro
                    let assump_159 := assump_42 assump_284
                    apply False.elim assump_159
            case inr assump_52 =>
              cases assump_52
              case inl assump_163 =>
                cases assump_38
                case inl assump_167 =>
                  cases assump_167
                  case inl assump_169 =>
                    cases assump_169
                    case inl assump_171 =>
                      have assump_285 : True := by
                        apply True.intro
                      let assump_177 := assump_42 assump_285
                      apply False.elim assump_177
                    case inr assump_172 =>
                      have assump_286 : True := by
                        apply True.intro
                      let assump_185 := assump_42 assump_286
                      apply False.elim assump_185
                  case inr assump_170 =>
                    cases assump_170
                    case inl assump_189 =>
                      have assump_287 : True := by
                        apply True.intro
                      let assump_195 := assump_42 assump_287
                      apply False.elim assump_195
                    case inr assump_190 =>
                      apply False.elim assump_190
                case inr assump_168 =>
                  cases assump_168
                  case inl assump_201 =>
                    have assump_288 : True := by
                      apply True.intro
                    let assump_207 := assump_42 assump_288
                    apply False.elim assump_207
                  case inr assump_202 =>
                    have assump_289 : True := by
                      apply True.intro
                    let assump_215 := assump_42 assump_289
                    apply False.elim assump_215
              case inr assump_164 =>
                cases assump_38
                case inl assump_221 =>
                  cases assump_221
                  case inl assump_223 =>
                    cases assump_223
                    case inl assump_225 =>
                      have assump_290 : True := by
                        apply True.intro
                      let assump_231 := assump_42 assump_290
                      apply False.elim assump_231
                    case inr assump_226 =>
                      have assump_291 : True := by
                        apply True.intro
                      let assump_239 := assump_42 assump_291
                      apply False.elim assump_239
                  case inr assump_224 =>
                    cases assump_224
                    case inl assump_243 =>
                      have assump_292 : True := by
                        apply True.intro
                      let assump_249 := assump_42 assump_292
                      apply False.elim assump_249
                    case inr assump_244 =>
                      apply False.elim assump_244
                case inr assump_222 =>
                  cases assump_222
                  case inl assump_255 =>
                    have assump_293 : True := by
                      apply True.intro
                    let assump_261 := assump_42 assump_293
                    apply False.elim assump_261
                  case inr assump_256 =>
                    have assump_294 : True := by
                      apply True.intro
                    let assump_269 := assump_42 assump_294
                    apply False.elim assump_269


variable (p4 p5 p1 p0 p2 p3 p7 p6 : Prop)
theorem file24_51507 : (((((p6 → False) ∧ (True ∧ p6)) ∧ ((p6 ∨ p0) ∧ (p5 → False))) → (((p7 → False) → False) → ((p2 → p5) → (p6 ∧ p7)))) ∨ ((((p1 → p0) ∧ (p3 → True)) ∨ ((p4 ∨ p3) → (p7 ∨ False))) → (((p4 → False) → False) ∧ ((True → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        cases assump_9
        case intro assump_20 assump_21 =>
          cases assump_20
          case inl assump_22 =>
            exact assump_22
          case inr assump_23 =>
            exact assump_15
  cases assump_1
  case intro assump_36 assump_37 =>
    cases assump_36
    case intro assump_38 assump_39 =>
      cases assump_39
      case intro assump_42 assump_43 =>
        cases assump_37
        case intro assump_48 assump_49 =>
          cases assump_48
          case inl assump_50 =>
            have assump_74 : p6 := by
              exact assump_50
            let assump_59 := assump_38 assump_74
            apply False.elim assump_59
          case inr assump_51 =>
            have assump_75 : p6 := by
              exact assump_43
            let assump_70 := assump_38 assump_75
            apply False.elim assump_70


variable (p0 p3 p1 p6 p2 p5 p4 : Prop)
theorem file24_52914 : ((((((p3 ∧ p2) → False) ∨ ((False ∧ p5) ∨ (p0 ∨ False))) → (((p0 ∧ p0) ∧ (p6 ∨ p5)) ∧ ((p0 → False) → (p4 ∧ True)))) ∧ ((((p1 ∨ p5) ∨ (p3 ∨ p2)) → False) ∧ (((p2 → p5) → (False ∨ True)) → ((False → True) ∧ (False ∨ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_25 : ((p2 → p5) → (False ∨ True)) := by
        intro assump_13
        apply Or.inr
        apply True.intro
      let assump_12 := assump_7 assump_25
      let assump_16 := And.right assump_12
      cases assump_16
      case inl assump_19 =>
        apply False.elim assump_19
      case inr assump_20 =>
        apply False.elim assump_20


variable (p2 p3 p1 p0 p5 : Prop)
theorem file24_53696 : (((((p5 ∨ p1) ∧ (p0 → p3)) ∨ ((p1 ∧ p3) → (p1 → False))) → False) → ((((False → False) ∧ (p2 ∨ True)) → False) ∧ (((False → False) → False) → ((True ∨ p2) → False)))) := by
  intro assump_5
  apply And.intro
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_8
    case inl assump_11 =>
      have assump_133 : (((p5 ∨ p1) ∧ (p0 → p3)) ∨ ((p1 ∧ p3) → (p1 → False))) := by
        apply Or.inr
        intro assump_18
        intro assump_19
        cases assump_18
        case intro assump_22 assump_23 =>
          have assump_134 : (((p5 ∨ p1) ∧ (p0 → p3)) ∨ ((p1 ∧ p3) → (p1 → False))) := by
            apply Or.inl
            apply And.intro
            apply Or.inr
            exact assump_22
            intro assump_32
            exact assump_23
          let assump_31 := assump_5 assump_134
          apply False.elim assump_31
      let assump_17 := assump_5 assump_133
      apply False.elim assump_17
    case inr assump_12 =>
      have assump_135 : (((p5 ∨ p1) ∧ (p0 → p3)) ∨ ((p1 ∧ p3) → (p1 → False))) := by
        apply Or.inr
        intro assump_46
        intro assump_47
        cases assump_46
        case intro assump_50 assump_51 =>
          have assump_136 : (((p5 ∨ p1) ∧ (p0 → p3)) ∨ ((p1 ∧ p3) → (p1 → False))) := by
            apply Or.inl
            apply And.intro
            apply Or.inr
            exact assump_50
            intro assump_60
            exact assump_51
          let assump_59 := assump_5 assump_136
          apply False.elim assump_59
      let assump_45 := assump_5 assump_135
      apply False.elim assump_45
  intro assump_69
  intro assump_70
  cases assump_70
  case inl assump_71 =>
    have assump_137 : (((p5 ∨ p1) ∧ (p0 → p3)) ∨ ((p1 ∧ p3) → (p1 → False))) := by
      apply Or.inr
      intro assump_80
      intro assump_81
      cases assump_80
      case intro assump_84 assump_85 =>
        have assump_138 : (((p5 ∨ p1) ∧ (p0 → p3)) ∨ ((p1 ∧ p3) → (p1 → False))) := by
          apply Or.inl
          apply And.intro
          apply Or.inr
          exact assump_84
          intro assump_94
          exact assump_85
        let assump_93 := assump_5 assump_138
        apply False.elim assump_93
    let assump_79 := assump_5 assump_137
    apply False.elim assump_79
  case inr assump_72 =>
    have assump_139 : (((p5 ∨ p1) ∧ (p0 → p3)) ∨ ((p1 ∧ p3) → (p1 → False))) := by
      apply Or.inr
      intro assump_110
      intro assump_111
      cases assump_110
      case intro assump_114 assump_115 =>
        have assump_140 : (((p5 ∨ p1) ∧ (p0 → p3)) ∨ ((p1 ∧ p3) → (p1 → False))) := by
          apply Or.inl
          apply And.intro
          apply Or.inr
          exact assump_114
          intro assump_124
          exact assump_115
        let assump_123 := assump_5 assump_140
        apply False.elim assump_123
    let assump_109 := assump_5 assump_139
    apply False.elim assump_109


variable (p1 p0 p4 p6 p3 : Prop)
theorem file24_56670 : (((((p1 ∨ p4) → False) → ((False ∧ p6) → (False ∨ False))) ∨ (((p3 → p0) ∨ (p1 → False)) → ((p6 → True) ∨ (p1 → p3)))) ∨ ((((False ∨ p3) ∧ (p6 → False)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3


variable (p1 p2 p5 p4 p0 : Prop)
theorem file24_57050 : (((((p4 → p5) → (p2 ∨ True)) ∨ ((p2 ∧ False) → False)) ∨ (((False → p5) → False) ∨ ((p0 → False) ∧ (p4 → False)))) ∨ ((((p4 ∧ p1) ∨ (True → False)) → ((p4 ∧ True) → False)) ∨ (((p2 → False) ∨ (False → p1)) ∨ ((p2 ∨ p0) → (True → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply True.intro


variable (p7 p0 p4 p5 p6 : Prop)
theorem file24_57449 : (((((p6 → p5) → (p0 → False)) ∧ ((False ∨ False) ∧ (p7 → False))) → False) ∨ ((((p0 → False) ∧ (p6 → False)) → ((p6 ∧ p4) ∨ (p0 → False))) → False)) := by
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
        apply False.elim assump_9


variable (p3 p4 p5 p1 p6 p7 : Prop)
theorem file24_57945 : (((((p6 → p6) → False) → ((p4 → False) ∨ (p1 → False))) → (((p5 → True) → (p3 ∨ True)) → ((p6 → p1) → (p5 → p5)))) ∨ ((((p3 ∨ False) ∨ (p4 ∨ p3)) → False) ∧ (((True → True) → False) ∨ ((False ∨ p7) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  exact assump_4


variable (p1 p0 p6 p2 p3 p5 p7 : Prop)
theorem file24_58324 : (((((p0 → False) → (p7 → True)) → ((p7 ∨ p5) ∧ (p1 ∨ False))) → (((p1 → p6) → False) → ((False → False) → False))) → ((((p5 ∨ False) → False) ∧ ((p5 ∨ True) → False)) → (((p2 ∧ False) → False) ∨ ((p5 ∧ p3) ∨ (p0 → p7))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inl
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      apply False.elim assump_13


variable (p3 p0 p2 p5 p6 p1 : Prop)
theorem file24_58825 : ((((((p2 → p1) → False) ∧ ((p6 → False) ∨ (p5 → False))) → (((p5 → False) ∧ (p0 ∨ p6)) → ((p5 ∧ p1) → (p3 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_47 : ((((p2 → p1) → False) ∧ ((p6 → False) ∨ (p5 → False))) → (((p5 → False) ∧ (p0 ∨ p6)) → ((p5 ∧ p1) → (p3 ∨ p1)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_6
      case intro assump_14 assump_15 =>
        cases assump_15
        case inl assump_18 =>
          cases assump_5
          case intro assump_22 assump_23 =>
            cases assump_23
            case inl assump_26 =>
              apply Or.inr
              exact assump_9
            case inr assump_27 =>
              apply Or.inr
              exact assump_9
        case inr assump_19 =>
          cases assump_5
          case intro assump_34 assump_35 =>
            cases assump_35
            case inl assump_38 =>
              apply Or.inr
              exact assump_9
            case inr assump_39 =>
              apply Or.inr
              exact assump_9
  let assump_4 := assump_1 assump_47
  apply False.elim assump_4


variable (p7 p5 p6 p3 p1 p0 : Prop)
theorem file24_60055 : (((((p0 ∧ p7) → (p3 → p7)) ∧ ((p1 ∨ False) → (False ∧ p6))) ∧ (((True ∨ p5) ∨ (p7 ∨ p7)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_16 : ((True ∨ p5) ∨ (p7 ∨ p7)) := by
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_12 := assump_3 assump_16
      apply False.elim assump_12


variable (p5 p3 p2 p0 p7 p6 p1 : Prop)
theorem file24_60552 : ((((((True ∨ p6) → (p0 → False)) ∧ ((p1 → False) ∨ (p6 ∧ p1))) ∧ (((p1 ∨ p1) ∧ (True → p7)) ∧ ((p0 ∧ True) → False))) ∧ ((((p5 → False) → False) ∧ ((p0 → True) → False)) ∧ (((p6 ∨ p3) ∧ (p7 ∨ p5)) → ((p2 → p5) ∧ (False → p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_5
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_16
              case inl assump_18 =>
                cases assump_3
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    have assump_120 : (p0 → True) := by
                      intro assump_38
                      apply True.intro
                    let assump_37 := assump_29 assump_120
                    apply False.elim assump_37
              case inr assump_19 =>
                cases assump_3
                case intro assump_48 assump_49 =>
                  cases assump_48
                  case intro assump_50 assump_51 =>
                    have assump_121 : (p0 → True) := by
                      intro assump_60
                      apply True.intro
                    let assump_59 := assump_51 assump_121
                    apply False.elim assump_59
        case inr assump_11 =>
          cases assump_11
          case intro assump_64 assump_65 =>
            cases assump_5
            case intro assump_70 assump_71 =>
              cases assump_70
              case intro assump_72 assump_73 =>
                cases assump_72
                case inl assump_74 =>
                  cases assump_3
                  case intro assump_82 assump_83 =>
                    cases assump_82
                    case intro assump_84 assump_85 =>
                      have assump_122 : (p0 → True) := by
                        intro assump_94
                        apply True.intro
                      let assump_93 := assump_85 assump_122
                      apply False.elim assump_93
                case inr assump_75 =>
                  cases assump_3
                  case intro assump_104 assump_105 =>
                    cases assump_104
                    case intro assump_106 assump_107 =>
                      have assump_123 : (p0 → True) := by
                        intro assump_116
                        apply True.intro
                      let assump_115 := assump_107 assump_123
                      apply False.elim assump_115


variable (p7 p4 p5 p6 : Prop)
theorem file24_63354 : ((((((p7 → p6) → (p5 ∧ p6)) → False) → False) ∧ ((((p4 ∨ True) → False) → False) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_23 : (((p4 ∨ True) → False) → False) := by
      intro assump_13
      have assump_24 : (p4 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_16 := assump_13 assump_24
      apply False.elim assump_16
    let assump_12 := assump_7 assump_23
    apply False.elim assump_12


variable (p6 p3 p2 p5 p0 p1 p7 : Prop)
theorem file24_63906 : (((((p6 ∨ p5) → False) ∧ ((p0 ∨ p1) ∧ (True ∧ p0))) → (((p6 → True) ∨ (False ∨ p2)) ∨ ((p5 ∧ True) ∧ (p3 ∨ p7)))) ∨ ((((p7 → p0) → False) ∨ ((p1 ∧ True) → (p1 ∨ p1))) ∨ (((p6 → p5) ∧ (p5 → p5)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          apply Or.inl
          apply Or.inl
          intro assump_18
          apply True.intro
      case inr assump_9 =>
        cases assump_7
        case intro assump_21 assump_22 =>
          apply Or.inl
          apply Or.inl
          intro assump_27
          apply True.intro


variable (p4 p2 p1 p7 : Prop)
theorem file24_64712 : (((((p7 ∧ p2) ∧ (False ∧ p4)) → False) → (((False ∧ p1) → False) → False)) → ((((p4 ∧ True) → (False ∨ p1)) → False) ∨ (((False → p4) → False) ∧ ((p1 → False) ∨ (p2 ∧ False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_31 : (((p7 ∧ p2) ∧ (False ∧ p4)) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_11
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
  let assump_8 := assump_1 assump_31
  have assump_32 : ((False ∧ p1) → False) := by
    intro assump_23
    cases assump_23
    case intro assump_24 assump_25 =>
      apply False.elim assump_24
  let assump_22 := assump_8 assump_32
  apply False.elim assump_22


variable (p4 p6 p0 : Prop)
theorem file24_65562 : (((((p6 → False) → (p0 → False)) → False) ∧ (((False → False) ∨ (p6 → False)) ∧ ((p6 ∧ p4) ∨ (p0 → False)))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_11
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        cases assump_15
        case inl assump_20 =>
          cases assump_20
          case intro assump_22 assump_23 =>
            have assump_101 : ((p6 → False) → (p0 → False)) := by
              intro assump_32
              intro assump_33
              have assump_102 : p6 := by
                exact assump_22
              let assump_38 := assump_32 assump_102
              apply False.elim assump_38
            let assump_31 := assump_10 assump_101
            apply False.elim assump_31
        case inr assump_21 =>
          have assump_103 : ((p6 → False) → (p0 → False)) := by
            intro assump_50
            intro assump_51
            have assump_104 : p0 := by
              exact assump_51
            let assump_58 := assump_21 assump_104
            apply False.elim assump_58
          let assump_49 := assump_10 assump_103
          apply False.elim assump_49
      case inr assump_17 =>
        cases assump_15
        case inl assump_67 =>
          cases assump_67
          case intro assump_69 assump_70 =>
            have assump_105 : p6 := by
              exact assump_69
            let assump_77 := assump_17 assump_105
            apply False.elim assump_77
        case inr assump_68 =>
          have assump_106 : ((p6 → False) → (p0 → False)) := by
            intro assump_86
            intro assump_87
            have assump_107 : p0 := by
              exact assump_87
            let assump_94 := assump_68 assump_107
            apply False.elim assump_94
          let assump_85 := assump_10 assump_106
          apply False.elim assump_85


variable (p0 p1 p3 p6 p4 p2 : Prop)
theorem file24_67525 : ((((((p2 ∨ p1) ∨ (p1 ∨ p6)) → False) ∧ (((p4 → False) ∧ (False ∧ p2)) → ((p0 ∨ p1) ∨ (p3 ∧ p3)))) ∧ ((((True ∧ p4) → (p0 ∨ True)) ∨ ((p4 ∧ p6) ∧ (p2 ∧ p4))) → False)) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      have assump_29 : (((True ∧ p4) → (p0 ∨ True)) ∨ ((p4 ∧ p6) ∧ (p2 ∧ p4))) := by
        apply Or.inl
        intro assump_19
        cases assump_19
        case intro assump_20 assump_21 =>
          apply Or.inr
          apply True.intro
      let assump_18 := assump_9 assump_29
      apply False.elim assump_18


variable (p1 p6 p7 p0 p3 p2 : Prop)
theorem file24_68213 : ((((((p0 → False) ∧ (p1 ∧ p2)) → ((p6 → p2) ∨ (p6 → False))) → False) ∧ ((((p6 → p2) ∧ (p7 → False)) → False) ∧ (((p0 ∧ p7) → False) ∧ ((p3 ∨ True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_20 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_16 := assump_11 assump_20
        apply False.elim assump_16


variable (p5 p1 p2 p0 p7 p3 p6 p4 : Prop)
theorem file24_68811 : (((((p2 → False) ∨ (p3 → False)) → ((False ∧ p1) → False)) → False) → ((((p5 → False) → False) ∧ ((p6 → False) → (p7 ∧ p1))) ∨ (((p3 ∧ p3) ∨ (p6 → False)) ∨ ((p5 → p4) ∨ (p0 → p1))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_45 : (((p2 → False) ∨ (p3 → False)) → ((False ∧ p1) → False)) := by
    intro assump_9
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      apply False.elim assump_11
  let assump_8 := assump_1 assump_45
  apply False.elim assump_8
  intro assump_18
  apply And.intro
  have assump_46 : (((p2 → False) ∨ (p3 → False)) → ((False ∧ p1) → False)) := by
    intro assump_23
    intro assump_24
    cases assump_24
    case intro assump_25 assump_26 =>
      apply False.elim assump_25
  let assump_22 := assump_1 assump_46
  apply False.elim assump_22
  have assump_47 : (((p2 → False) ∨ (p3 → False)) → ((False ∧ p1) → False)) := by
    intro assump_36
    intro assump_37
    cases assump_37
    case intro assump_38 assump_39 =>
      apply False.elim assump_38
  let assump_35 := assump_1 assump_47
  apply False.elim assump_35


variable (p4 p1 p5 p6 p2 : Prop)
theorem file24_69998 : (((((p4 ∧ p4) ∨ (False → False)) ∨ ((p4 → False) ∨ (True → p6))) ∨ (((p2 → False) ∨ (p1 → False)) ∨ ((True → False) ∨ (False → False)))) ∨ ((((True → p5) → (p6 ∨ p4)) → ((False → False) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_12
  apply False.elim assump_12


variable (p3 p6 p2 p5 p0 p4 p7 p1 : Prop)
theorem file24_70383 : (((((p6 ∧ p1) → (True ∨ True)) ∨ ((p2 → False) ∨ (p5 ∨ p5))) ∨ (((p6 → False) ∧ (p7 → False)) ∨ ((True → p1) → (p6 → p4)))) ∨ ((((p0 ∧ p2) → (p6 ∧ p2)) → ((True → False) → (p3 ∨ p6))) ∧ (((p3 ∧ p6) → (p0 → False)) → ((p1 ∨ p6) ∨ (p7 → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply True.intro


variable (p7 p0 p3 p5 p2 p6 p4 : Prop)
theorem file24_70849 : (((((p5 ∧ p6) → (False → p5)) ∨ ((p4 ∧ p3) → False)) ∨ (((p0 → p2) ∧ (p0 ∧ p3)) → False)) ∨ ((((p0 → p3) → (True → p7)) ∧ ((p0 ∨ False) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply False.elim assump_2


variable (p7 p1 p2 p0 p5 p3 : Prop)
theorem file24_71178 : ((((((p7 → p3) → False) → ((p3 → False) ∨ (p7 ∨ p3))) ∨ (((p3 → p3) ∧ (p1 → p0)) ∨ ((True ∨ False) ∧ (p5 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p7 → p3) → False) → ((p3 → False) ∨ (p7 ∨ p3))) ∨ (((p3 → p3) ∧ (p1 → p0)) ∨ ((True ∨ False) ∧ (p5 ∧ p2)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_23 : (p7 → p3) := by
      intro assump_13
      exact assump_8
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p5 p4 p0 p3 p2 p6 p7 p1 : Prop)
theorem file24_71824 : ((((((p5 ∨ p3) ∨ (p2 ∧ p7)) → ((p2 → p6) ∧ (True → True))) → (((True → p5) ∨ (p7 ∧ p4)) ∧ ((p7 ∨ p5) ∨ (False → p4)))) ∧ ((((p1 ∧ p3) ∧ (p0 ∨ False)) ∧ ((p7 → False) → False)) ∧ (((p2 ∧ True) → (False → p3)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_11
            case inl assump_18 =>
              have assump_36 : ((p2 ∧ True) → (False → p3)) := by
                intro assump_27
                intro assump_28
                apply False.elim assump_28
              let assump_26 := assump_7 assump_36
              apply False.elim assump_26
            case inr assump_19 =>
              apply False.elim assump_19


variable (p4 p5 p2 p1 p0 p7 : Prop)
theorem file24_72836 : ((((((False → False) ∨ (p5 ∧ True)) ∨ ((p2 ∧ p7) → (p1 → p7))) ∨ (((p2 → False) → (p4 → p7)) ∧ ((p0 ∧ p5) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → False) ∨ (p5 ∧ True)) ∨ ((p2 ∧ p7) → (p1 → p7))) ∨ (((p2 → False) → (p4 → p7)) ∧ ((p0 ∧ p5) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p3 p0 p5 p2 p6 p7 p1 : Prop)
theorem file24_73365 : (((((p3 ∧ p0) → False) ∨ ((p0 ∧ p2) → (False → p1))) ∨ (((p7 ∧ p6) ∧ (p1 ∨ p0)) ∨ ((p0 ∧ p5) ∨ (p5 → True)))) → ((((p1 ∧ p6) ∧ (p4 → p7)) ∧ ((True ∨ p7) ∨ (p2 ∨ p4))) → (((p6 ∨ p2) ∧ (p1 ∨ False)) ∧ ((False ∨ p2) → (p2 ∨ p6))))) := by
  intro assump_25
  intro assump_26
  apply And.intro
  apply And.intro
  cases assump_26
  case intro assump_27 assump_28 =>
    cases assump_27
    case intro assump_29 assump_30 =>
      cases assump_29
      case intro assump_31 assump_32 =>
        cases assump_28
        case inl assump_39 =>
          cases assump_39
          case inl assump_41 =>
            cases assump_25
            case inl assump_45 =>
              cases assump_45
              case inl assump_47 =>
                apply Or.inl
                exact assump_32
              case inr assump_48 =>
                apply Or.inl
                exact assump_32
            case inr assump_46 =>
              cases assump_46
              case inl assump_53 =>
                cases assump_53
                case intro assump_55 assump_56 =>
                  cases assump_55
                  case intro assump_57 assump_58 =>
                    cases assump_56
                    case inl assump_63 =>
                      apply Or.inl
                      exact assump_58
                    case inr assump_64 =>
                      apply Or.inl
                      exact assump_58
              case inr assump_54 =>
                cases assump_54
                case inl assump_69 =>
                  cases assump_69
                  case intro assump_71 assump_72 =>
                    apply Or.inl
                    exact assump_32
                case inr assump_70 =>
                  apply Or.inl
                  exact assump_32
          case inr assump_42 =>
            cases assump_25
            case inl assump_81 =>
              cases assump_81
              case inl assump_83 =>
                apply Or.inl
                exact assump_32
              case inr assump_84 =>
                apply Or.inl
                exact assump_32
            case inr assump_82 =>
              cases assump_82
              case inl assump_89 =>
                cases assump_89
                case intro assump_91 assump_92 =>
                  cases assump_91
                  case intro assump_93 assump_94 =>
                    cases assump_92
                    case inl assump_99 =>
                      apply Or.inl
                      exact assump_94
                    case inr assump_100 =>
                      apply Or.inl
                      exact assump_94
              case inr assump_90 =>
                cases assump_90
                case inl assump_105 =>
                  cases assump_105
                  case intro assump_107 assump_108 =>
                    apply Or.inl
                    exact assump_32
                case inr assump_106 =>
                  apply Or.inl
                  exact assump_32
        case inr assump_40 =>
          cases assump_40
          case inl assump_115 =>
            cases assump_25
            case inl assump_119 =>
              cases assump_119
              case inl assump_121 =>
                apply Or.inl
                exact assump_32
              case inr assump_122 =>
                apply Or.inl
                exact assump_32
            case inr assump_120 =>
              cases assump_120
              case inl assump_127 =>
                cases assump_127
                case intro assump_129 assump_130 =>
                  cases assump_129
                  case intro assump_131 assump_132 =>
                    cases assump_130
                    case inl assump_137 =>
                      apply Or.inl
                      exact assump_132
                    case inr assump_138 =>
                      apply Or.inl
                      exact assump_132
              case inr assump_128 =>
                cases assump_128
                case inl assump_143 =>
                  cases assump_143
                  case intro assump_145 assump_146 =>
                    apply Or.inl
                    exact assump_32
                case inr assump_144 =>
                  apply Or.inl
                  exact assump_32
          case inr assump_116 =>
            cases assump_25
            case inl assump_155 =>
              cases assump_155
              case inl assump_157 =>
                apply Or.inl
                exact assump_32
              case inr assump_158 =>
                apply Or.inl
                exact assump_32
            case inr assump_156 =>
              cases assump_156
              case inl assump_163 =>
                cases assump_163
                case intro assump_165 assump_166 =>
                  cases assump_165
                  case intro assump_167 assump_168 =>
                    cases assump_166
                    case inl assump_173 =>
                      apply Or.inl
                      exact assump_168
                    case inr assump_174 =>
                      apply Or.inl
                      exact assump_168
              case inr assump_164 =>
                cases assump_164
                case inl assump_179 =>
                  cases assump_179
                  case intro assump_181 assump_182 =>
                    apply Or.inl
                    exact assump_32
                case inr assump_180 =>
                  apply Or.inl
                  exact assump_32
  cases assump_26
  case intro assump_189 assump_190 =>
    cases assump_189
    case intro assump_191 assump_192 =>
      cases assump_191
      case intro assump_193 assump_194 =>
        cases assump_190
        case inl assump_201 =>
          cases assump_201
          case inl assump_203 =>
            cases assump_25
            case inl assump_207 =>
              cases assump_207
              case inl assump_209 =>
                apply Or.inl
                exact assump_193
              case inr assump_210 =>
                apply Or.inl
                exact assump_193
            case inr assump_208 =>
              cases assump_208
              case inl assump_215 =>
                cases assump_215
                case intro assump_217 assump_218 =>
                  cases assump_217
                  case intro assump_219 assump_220 =>
                    cases assump_218
                    case inl assump_225 =>
                      apply Or.inl
                      exact assump_225
                    case inr assump_226 =>
                      apply Or.inl
                      exact assump_193
              case inr assump_216 =>
                cases assump_216
                case inl assump_231 =>
                  cases assump_231
                  case intro assump_233 assump_234 =>
                    apply Or.inl
                    exact assump_193
                case inr assump_232 =>
                  apply Or.inl
                  exact assump_193
          case inr assump_204 =>
            cases assump_25
            case inl assump_243 =>
              cases assump_243
              case inl assump_245 =>
                apply Or.inl
                exact assump_193
              case inr assump_246 =>
                apply Or.inl
                exact assump_193
            case inr assump_244 =>
              cases assump_244
              case inl assump_251 =>
                cases assump_251
                case intro assump_253 assump_254 =>
                  cases assump_253
                  case intro assump_255 assump_256 =>
                    cases assump_254
                    case inl assump_261 =>
                      apply Or.inl
                      exact assump_261
                    case inr assump_262 =>
                      apply Or.inl
                      exact assump_193
              case inr assump_252 =>
                cases assump_252
                case inl assump_267 =>
                  cases assump_267
                  case intro assump_269 assump_270 =>
                    apply Or.inl
                    exact assump_193
                case inr assump_268 =>
                  apply Or.inl
                  exact assump_193
        case inr assump_202 =>
          cases assump_202
          case inl assump_277 =>
            cases assump_25
            case inl assump_281 =>
              cases assump_281
              case inl assump_283 =>
                apply Or.inl
                exact assump_193
              case inr assump_284 =>
                apply Or.inl
                exact assump_193
            case inr assump_282 =>
              cases assump_282
              case inl assump_289 =>
                cases assump_289
                case intro assump_291 assump_292 =>
                  cases assump_291
                  case intro assump_293 assump_294 =>
                    cases assump_292
                    case inl assump_299 =>
                      apply Or.inl
                      exact assump_299
                    case inr assump_300 =>
                      apply Or.inl
                      exact assump_193
              case inr assump_290 =>
                cases assump_290
                case inl assump_305 =>
                  cases assump_305
                  case intro assump_307 assump_308 =>
                    apply Or.inl
                    exact assump_193
                case inr assump_306 =>
                  apply Or.inl
                  exact assump_193
          case inr assump_278 =>
            cases assump_25
            case inl assump_317 =>
              cases assump_317
              case inl assump_319 =>
                apply Or.inl
                exact assump_193
              case inr assump_320 =>
                apply Or.inl
                exact assump_193
            case inr assump_318 =>
              cases assump_318
              case inl assump_325 =>
                cases assump_325
                case intro assump_327 assump_328 =>
                  cases assump_327
                  case intro assump_329 assump_330 =>
                    cases assump_328
                    case inl assump_335 =>
                      apply Or.inl
                      exact assump_335
                    case inr assump_336 =>
                      apply Or.inl
                      exact assump_193
              case inr assump_326 =>
                cases assump_326
                case inl assump_341 =>
                  cases assump_341
                  case intro assump_343 assump_344 =>
                    apply Or.inl
                    exact assump_193
                case inr assump_342 =>
                  apply Or.inl
                  exact assump_193
  intro assump_351
  cases assump_351
  case inl assump_352 =>
    apply False.elim assump_352
  case inr assump_353 =>
    cases assump_26
    case intro assump_358 assump_359 =>
      cases assump_358
      case intro assump_360 assump_361 =>
        cases assump_360
        case intro assump_362 assump_363 =>
          cases assump_359
          case inl assump_370 =>
            cases assump_370
            case inl assump_372 =>
              cases assump_25
              case inl assump_376 =>
                cases assump_376
                case inl assump_378 =>
                  apply Or.inl
                  exact assump_353
                case inr assump_379 =>
                  apply Or.inl
                  exact assump_353
              case inr assump_377 =>
                cases assump_377
                case inl assump_384 =>
                  cases assump_384
                  case intro assump_386 assump_387 =>
                    cases assump_386
                    case intro assump_388 assump_389 =>
                      cases assump_387
                      case inl assump_394 =>
                        apply Or.inl
                        exact assump_353
                      case inr assump_395 =>
                        apply Or.inl
                        exact assump_353
                case inr assump_385 =>
                  cases assump_385
                  case inl assump_400 =>
                    cases assump_400
                    case intro assump_402 assump_403 =>
                      apply Or.inl
                      exact assump_353
                  case inr assump_401 =>
                    apply Or.inl
                    exact assump_353
            case inr assump_373 =>
              cases assump_25
              case inl assump_412 =>
                cases assump_412
                case inl assump_414 =>
                  apply Or.inl
                  exact assump_353
                case inr assump_415 =>
                  apply Or.inl
                  exact assump_353
              case inr assump_413 =>
                cases assump_413
                case inl assump_420 =>
                  cases assump_420
                  case intro assump_422 assump_423 =>
                    cases assump_422
                    case intro assump_424 assump_425 =>
                      cases assump_423
                      case inl assump_430 =>
                        apply Or.inl
                        exact assump_353
                      case inr assump_431 =>
                        apply Or.inl
                        exact assump_353
                case inr assump_421 =>
                  cases assump_421
                  case inl assump_436 =>
                    cases assump_436
                    case intro assump_438 assump_439 =>
                      apply Or.inl
                      exact assump_353
                  case inr assump_437 =>
                    apply Or.inl
                    exact assump_353
          case inr assump_371 =>
            cases assump_371
            case inl assump_446 =>
              cases assump_25
              case inl assump_450 =>
                cases assump_450
                case inl assump_452 =>
                  apply Or.inl
                  exact assump_446
                case inr assump_453 =>
                  apply Or.inl
                  exact assump_446
              case inr assump_451 =>
                cases assump_451
                case inl assump_458 =>
                  cases assump_458
                  case intro assump_460 assump_461 =>
                    cases assump_460
                    case intro assump_462 assump_463 =>
                      cases assump_461
                      case inl assump_468 =>
                        apply Or.inl
                        exact assump_446
                      case inr assump_469 =>
                        apply Or.inl
                        exact assump_446
                case inr assump_459 =>
                  cases assump_459
                  case inl assump_474 =>
                    cases assump_474
                    case intro assump_476 assump_477 =>
                      apply Or.inl
                      exact assump_446
                  case inr assump_475 =>
                    apply Or.inl
                    exact assump_446
            case inr assump_447 =>
              cases assump_25
              case inl assump_486 =>
                cases assump_486
                case inl assump_488 =>
                  apply Or.inl
                  exact assump_353
                case inr assump_489 =>
                  apply Or.inl
                  exact assump_353
              case inr assump_487 =>
                cases assump_487
                case inl assump_494 =>
                  cases assump_494
                  case intro assump_496 assump_497 =>
                    cases assump_496
                    case intro assump_498 assump_499 =>
                      cases assump_497
                      case inl assump_504 =>
                        apply Or.inl
                        exact assump_353
                      case inr assump_505 =>
                        apply Or.inl
                        exact assump_353
                case inr assump_495 =>
                  cases assump_495
                  case inl assump_510 =>
                    cases assump_510
                    case intro assump_512 assump_513 =>
                      apply Or.inl
                      exact assump_353
                  case inr assump_511 =>
                    apply Or.inl
                    exact assump_353


variable (p3 p4 p7 p5 p0 : Prop)
theorem file24_89989 : ((((((p0 → p0) ∨ (p7 ∨ p5)) → False) → False) ∧ ((((p3 → False) → False) ∧ ((p3 ∨ True) → False)) ∧ (((p7 ∧ True) ∨ (p4 → p0)) ∨ ((p5 ∨ p0) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          cases assump_14
          case inl assump_16 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              have assump_43 : (p3 ∨ True) := by
                apply Or.inr
                apply True.intro
              let assump_25 := assump_9 assump_43
              apply False.elim assump_25
          case inr assump_17 =>
            have assump_44 : (p3 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_32 := assump_9 assump_44
            apply False.elim assump_32
        case inr assump_15 =>
          have assump_45 : (p3 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_39 := assump_9 assump_45
          apply False.elim assump_39


variable (p0 p6 p2 p1 p5 p3 : Prop)
theorem file24_91221 : (((((True ∨ p6) ∧ (p0 ∨ p3)) ∨ ((p1 ∧ p3) → (p3 → False))) ∧ (((False → False) ∧ (p2 → p2)) → False)) → ((((True ∧ p3) → (p5 ∨ p2)) ∨ ((p1 ∧ p3) ∨ (p3 → p3))) ∧ (((p1 ∨ p0) → (p5 → False)) → False))) := by
  intro assump_33
  apply And.intro
  cases assump_33
  case intro assump_34 assump_35 =>
    cases assump_34
    case inl assump_36 =>
      cases assump_36
      case intro assump_38 assump_39 =>
        cases assump_38
        case inl assump_40 =>
          cases assump_39
          case inl assump_44 =>
            apply Or.inl
            intro assump_50
            cases assump_50
            case intro assump_51 assump_52 =>
              have assump_249 : ((False → False) ∧ (p2 → p2)) := by
                apply And.intro
                intro assump_59
                apply False.elim assump_59
                intro assump_62
                exact assump_62
              let assump_58 := assump_35 assump_249
              apply False.elim assump_58
          case inr assump_45 =>
            apply Or.inl
            intro assump_72
            cases assump_72
            case intro assump_73 assump_74 =>
              have assump_250 : ((False → False) ∧ (p2 → p2)) := by
                apply And.intro
                intro assump_81
                apply False.elim assump_81
                intro assump_84
                exact assump_84
              let assump_80 := assump_35 assump_250
              apply False.elim assump_80
        case inr assump_41 =>
          cases assump_39
          case inl assump_92 =>
            apply Or.inl
            intro assump_98
            cases assump_98
            case intro assump_99 assump_100 =>
              have assump_251 : ((False → False) ∧ (p2 → p2)) := by
                apply And.intro
                intro assump_107
                apply False.elim assump_107
                intro assump_110
                exact assump_110
              let assump_106 := assump_35 assump_251
              apply False.elim assump_106
          case inr assump_93 =>
            apply Or.inl
            intro assump_120
            cases assump_120
            case intro assump_121 assump_122 =>
              have assump_252 : ((False → False) ∧ (p2 → p2)) := by
                apply And.intro
                intro assump_129
                apply False.elim assump_129
                intro assump_132
                exact assump_132
              let assump_128 := assump_35 assump_252
              apply False.elim assump_128
    case inr assump_37 =>
      apply Or.inl
      intro assump_142
      cases assump_142
      case intro assump_143 assump_144 =>
        have assump_253 : ((False → False) ∧ (p2 → p2)) := by
          apply And.intro
          intro assump_151
          apply False.elim assump_151
          intro assump_154
          exact assump_154
        let assump_150 := assump_35 assump_253
        apply False.elim assump_150
  intro assump_160
  cases assump_33
  case intro assump_163 assump_164 =>
    cases assump_163
    case inl assump_165 =>
      cases assump_165
      case intro assump_167 assump_168 =>
        cases assump_167
        case inl assump_169 =>
          cases assump_168
          case inl assump_173 =>
            have assump_254 : ((False → False) ∧ (p2 → p2)) := by
              apply And.intro
              intro assump_180
              apply False.elim assump_180
              intro assump_183
              exact assump_183
            let assump_179 := assump_164 assump_254
            apply False.elim assump_179
          case inr assump_174 =>
            have assump_255 : ((False → False) ∧ (p2 → p2)) := by
              apply And.intro
              intro assump_194
              apply False.elim assump_194
              intro assump_197
              exact assump_197
            let assump_193 := assump_164 assump_255
            apply False.elim assump_193
        case inr assump_170 =>
          cases assump_168
          case inl assump_205 =>
            have assump_256 : ((False → False) ∧ (p2 → p2)) := by
              apply And.intro
              intro assump_212
              apply False.elim assump_212
              intro assump_215
              exact assump_215
            let assump_211 := assump_164 assump_256
            apply False.elim assump_211
          case inr assump_206 =>
            have assump_257 : ((False → False) ∧ (p2 → p2)) := by
              apply And.intro
              intro assump_226
              apply False.elim assump_226
              intro assump_229
              exact assump_229
            let assump_225 := assump_164 assump_257
            apply False.elim assump_225
    case inr assump_166 =>
      have assump_258 : ((False → False) ∧ (p2 → p2)) := by
        apply And.intro
        intro assump_240
        apply False.elim assump_240
        intro assump_243
        exact assump_243
      let assump_239 := assump_164 assump_258
      apply False.elim assump_239


variable (p3 p1 p0 : Prop)
theorem file24_96271 : (((((p3 ∧ True) → (True ∨ p0)) ∧ ((False ∨ p1) ∨ (p1 → True))) → False) → False) := by
  intro assump_1
  have assump_16 : (((p3 ∧ True) → (True ∨ p0)) ∧ ((False ∨ p1) ∨ (p1 → True))) := by
    apply And.intro
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply True.intro
    apply Or.inr
    intro assump_12
    apply True.intro
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p4 p1 p6 p2 p7 : Prop)
theorem file24_96777 : ((((((p7 ∨ False) → (p2 → False)) → False) ∧ (((p4 → False) → (p6 → p4)) ∧ ((p1 ∨ p6) ∧ (p2 ∧ False)))) ∨ ((((p6 → False) ∧ (p4 ∧ False)) → ((p1 ∧ p4) ∨ (False ∨ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_13
            case intro assump_18 assump_19 =>
              apply False.elim assump_19
          case inr assump_15 =>
            cases assump_13
            case intro assump_26 assump_27 =>
              apply False.elim assump_27
  case inr assump_3 =>
    have assump_49 : (((p6 → False) ∧ (p4 ∧ False)) → ((p1 ∧ p4) ∨ (False ∨ False))) := by
      intro assump_35
      cases assump_35
      case intro assump_36 assump_37 =>
        cases assump_37
        case intro assump_40 assump_41 =>
          apply False.elim assump_41
    let assump_34 := assump_3 assump_49
    apply False.elim assump_34


variable (p0 p1 p5 p7 p4 : Prop)
theorem file24_97958 : ((((((p5 ∧ False) → False) → ((p7 ∨ p0) ∧ (p7 → p4))) → False) ∧ ((((p0 ∨ p1) ∨ (p7 ∨ False)) ∨ ((p0 ∨ p0) → (True ∧ p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_29 : (((p0 ∨ p1) ∨ (p7 ∨ False)) ∨ ((p0 ∨ p0) → (True ∧ p4))) := by
      apply Or.inr
      intro assump_9
      apply And.intro
      apply True.intro
      cases assump_9
      case inl assump_10 =>
        have assump_30 : (((p0 ∨ p1) ∨ (p7 ∨ False)) ∨ ((p0 ∨ p0) → (True ∧ p4))) := by
          apply Or.inl
          apply Or.inl
          apply Or.inl
          exact assump_10
        let assump_15 := assump_3 assump_30
        apply False.elim assump_15
      case inr assump_11 =>
        have assump_31 : (((p0 ∨ p1) ∨ (p7 ∨ False)) ∨ ((p0 ∨ p0) → (True ∧ p4))) := by
          apply Or.inl
          apply Or.inl
          apply Or.inl
          exact assump_11
        let assump_22 := assump_3 assump_31
        apply False.elim assump_22
    let assump_8 := assump_3 assump_29
    apply False.elim assump_8


variable (p3 p1 p4 p0 p7 p5 p2 : Prop)
theorem file24_99076 : ((((((p5 ∨ p5) ∨ (p2 ∧ False)) → ((p7 ∧ True) ∨ (p2 ∧ p2))) → False) ∧ ((((p1 → p0) → False) ∧ ((p0 ∧ p7) ∨ (p1 ∧ p2))) ∧ (((p3 ∧ p5) ∨ (p1 ∧ p4)) ∧ ((p0 ∧ True) ∧ (p7 ∨ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_7
            case intro assump_20 assump_21 =>
              cases assump_20
              case inl assump_22 =>
                cases assump_22
                case intro assump_24 assump_25 =>
                  cases assump_21
                  case intro assump_30 assump_31 =>
                    cases assump_30
                    case intro assump_32 assump_33 =>
                      cases assump_31
                      case inl assump_38 =>
                        have assump_218 : (p1 → p0) := by
                          intro assump_49
                          exact assump_32
                        let assump_48 := assump_8 assump_218
                        apply False.elim assump_48
                      case inr assump_39 =>
                        have assump_219 : (p1 → p0) := by
                          intro assump_64
                          exact assump_32
                        let assump_63 := assump_8 assump_219
                        apply False.elim assump_63
              case inr assump_23 =>
                cases assump_23
                case intro assump_70 assump_71 =>
                  cases assump_21
                  case intro assump_76 assump_77 =>
                    cases assump_76
                    case intro assump_78 assump_79 =>
                      cases assump_77
                      case inl assump_84 =>
                        have assump_220 : (p1 → p0) := by
                          intro assump_95
                          exact assump_78
                        let assump_94 := assump_8 assump_220
                        apply False.elim assump_94
                      case inr assump_85 =>
                        have assump_221 : (p1 → p0) := by
                          intro assump_110
                          exact assump_78
                        let assump_109 := assump_8 assump_221
                        apply False.elim assump_109
        case inr assump_13 =>
          cases assump_13
          case intro assump_116 assump_117 =>
            cases assump_7
            case intro assump_122 assump_123 =>
              cases assump_122
              case inl assump_124 =>
                cases assump_124
                case intro assump_126 assump_127 =>
                  cases assump_123
                  case intro assump_132 assump_133 =>
                    cases assump_132
                    case intro assump_134 assump_135 =>
                      cases assump_133
                      case inl assump_140 =>
                        have assump_222 : (p1 → p0) := by
                          intro assump_151
                          exact assump_134
                        let assump_150 := assump_8 assump_222
                        apply False.elim assump_150
                      case inr assump_141 =>
                        have assump_223 : (p1 → p0) := by
                          intro assump_166
                          exact assump_134
                        let assump_165 := assump_8 assump_223
                        apply False.elim assump_165
              case inr assump_125 =>
                cases assump_125
                case intro assump_172 assump_173 =>
                  cases assump_123
                  case intro assump_178 assump_179 =>
                    cases assump_178
                    case intro assump_180 assump_181 =>
                      cases assump_179
                      case inl assump_186 =>
                        have assump_224 : (p1 → p0) := by
                          intro assump_197
                          exact assump_180
                        let assump_196 := assump_8 assump_224
                        apply False.elim assump_196
                      case inr assump_187 =>
                        have assump_225 : (p1 → p0) := by
                          intro assump_212
                          exact assump_180
                        let assump_211 := assump_8 assump_225
                        apply False.elim assump_211


variable (p1 p6 p7 p5 p2 p0 p3 : Prop)
theorem file24_103705 : (((((False → True) ∧ (p0 ∧ p3)) → ((p5 → p0) ∧ (p3 ∨ p1))) → False) → ((((True ∨ p3) ∨ (p2 → False)) → ((False → True) ∧ (p7 ∧ p6))) ∨ (((False → p6) → False) → ((True ∧ False) ∨ (p2 → False))))) := by
  intro assump_9
  apply Or.inl
  intro assump_12
  apply And.intro
  intro assump_13
  apply True.intro
  apply And.intro
  cases assump_12
  case inl assump_14 =>
    cases assump_14
    case inl assump_16 =>
      have assump_206 : (((False → True) ∧ (p0 ∧ p3)) → ((p5 → p0) ∧ (p3 ∨ p1))) := by
        intro assump_21
        apply And.intro
        intro assump_22
        cases assump_21
        case intro assump_25 assump_26 =>
          cases assump_26
          case intro assump_29 assump_30 =>
            exact assump_29
        cases assump_21
        case intro assump_35 assump_36 =>
          cases assump_36
          case intro assump_39 assump_40 =>
            apply Or.inl
            exact assump_40
      let assump_20 := assump_9 assump_206
      apply False.elim assump_20
    case inr assump_17 =>
      have assump_207 : (((False → True) ∧ (p0 ∧ p3)) → ((p5 → p0) ∧ (p3 ∨ p1))) := by
        intro assump_52
        apply And.intro
        intro assump_53
        cases assump_52
        case intro assump_56 assump_57 =>
          cases assump_57
          case intro assump_60 assump_61 =>
            exact assump_60
        cases assump_52
        case intro assump_66 assump_67 =>
          cases assump_67
          case intro assump_70 assump_71 =>
            apply Or.inl
            exact assump_71
      let assump_51 := assump_9 assump_207
      apply False.elim assump_51
  case inr assump_15 =>
    have assump_208 : (((False → True) ∧ (p0 ∧ p3)) → ((p5 → p0) ∧ (p3 ∨ p1))) := by
      intro assump_83
      apply And.intro
      intro assump_84
      cases assump_83
      case intro assump_87 assump_88 =>
        cases assump_88
        case intro assump_91 assump_92 =>
          exact assump_91
      cases assump_83
      case intro assump_97 assump_98 =>
        cases assump_98
        case intro assump_101 assump_102 =>
          apply Or.inl
          exact assump_102
    let assump_82 := assump_9 assump_208
    apply False.elim assump_82
  cases assump_12
  case inl assump_110 =>
    cases assump_110
    case inl assump_112 =>
      have assump_209 : (((False → True) ∧ (p0 ∧ p3)) → ((p5 → p0) ∧ (p3 ∨ p1))) := by
        intro assump_117
        apply And.intro
        intro assump_118
        cases assump_117
        case intro assump_121 assump_122 =>
          cases assump_122
          case intro assump_125 assump_126 =>
            exact assump_125
        cases assump_117
        case intro assump_131 assump_132 =>
          cases assump_132
          case intro assump_135 assump_136 =>
            apply Or.inl
            exact assump_136
      let assump_116 := assump_9 assump_209
      apply False.elim assump_116
    case inr assump_113 =>
      have assump_210 : (((False → True) ∧ (p0 ∧ p3)) → ((p5 → p0) ∧ (p3 ∨ p1))) := by
        intro assump_148
        apply And.intro
        intro assump_149
        cases assump_148
        case intro assump_152 assump_153 =>
          cases assump_153
          case intro assump_156 assump_157 =>
            exact assump_156
        cases assump_148
        case intro assump_162 assump_163 =>
          cases assump_163
          case intro assump_166 assump_167 =>
            apply Or.inl
            exact assump_167
      let assump_147 := assump_9 assump_210
      apply False.elim assump_147
  case inr assump_111 =>
    have assump_211 : (((False → True) ∧ (p0 ∧ p3)) → ((p5 → p0) ∧ (p3 ∨ p1))) := by
      intro assump_179
      apply And.intro
      intro assump_180
      cases assump_179
      case intro assump_183 assump_184 =>
        cases assump_184
        case intro assump_187 assump_188 =>
          exact assump_187
      cases assump_179
      case intro assump_193 assump_194 =>
        cases assump_194
        case intro assump_197 assump_198 =>
          apply Or.inl
          exact assump_198
    let assump_178 := assump_9 assump_211
    apply False.elim assump_178


variable (p6 : Prop)
theorem file24_107873 : ((((((True ∧ p6) → (False → True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_17 : ((((True ∧ p6) → (False → True)) → False) → False) := by
    intro assump_5
    have assump_18 : ((True ∧ p6) → (False → True)) := by
      intro assump_9
      intro assump_10
      apply True.intro
    let assump_8 := assump_5 assump_18
    apply False.elim assump_8
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p0 p2 p6 p3 p7 p5 p4 p1 : Prop)
theorem file24_108386 : (((((False → False) → (p4 → False)) → False) → (((p4 ∧ p1) → (False ∧ p2)) → False)) → ((((False → p0) ∨ (p5 ∨ False)) ∨ ((False → False) ∨ (p0 → p6))) ∨ (((p3 → False) → (p7 → False)) ∧ ((p6 → False) → (p4 → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p6 p1 : Prop)
theorem file24_108767 : ((((((True ∧ p6) → (p1 → False)) → False) → False) ∧ ((((False → False) → False) → ((True → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((False → False) → False) → ((True → False) → False)) := by
      intro assump_9
      intro assump_10
      have assump_26 : (False → False) := by
        intro assump_16
        apply False.elim assump_16
      let assump_15 := assump_9 assump_26
      apply False.elim assump_15
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p7 p2 p6 p0 p1 p3 p5 p4 : Prop)
theorem file24_109408 : (((((True ∨ p1) ∧ (p3 → False)) ∨ ((p6 → p1) ∨ (False ∨ p3))) ∧ (((p6 → p2) → False) ∧ ((p6 ∨ p1) → False))) → ((((p5 → False) ∨ (p0 ∧ True)) ∨ ((p2 ∨ p3) → False)) ∧ (((p6 ∧ p0) → False) ∧ ((False → p4) → (p7 ∧ p2))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            apply Or.inl
            apply Or.inl
            intro assump_20
            have assump_378 : (p6 → p2) := by
              intro assump_26
              have assump_379 : (p6 ∨ p1) := by
                apply Or.inl
                exact assump_26
              let assump_31 := assump_15 assump_379
              apply False.elim assump_31
            let assump_25 := assump_14 assump_378
            apply False.elim assump_25
        case inr assump_9 =>
          cases assump_3
          case intro assump_42 assump_43 =>
            apply Or.inl
            apply Or.inl
            intro assump_48
            have assump_380 : (p6 ∨ p1) := by
              apply Or.inr
              exact assump_9
            let assump_52 := assump_43 assump_380
            apply False.elim assump_52
    case inr assump_5 =>
      cases assump_5
      case inl assump_56 =>
        cases assump_3
        case intro assump_60 assump_61 =>
          apply Or.inl
          apply Or.inl
          intro assump_66
          have assump_381 : (p6 → p2) := by
            intro assump_72
            have assump_382 : (p6 ∨ p1) := by
              apply Or.inl
              exact assump_72
            let assump_77 := assump_61 assump_382
            apply False.elim assump_77
          let assump_71 := assump_60 assump_381
          apply False.elim assump_71
      case inr assump_57 =>
        cases assump_57
        case inl assump_84 =>
          apply False.elim assump_84
        case inr assump_85 =>
          cases assump_3
          case intro assump_90 assump_91 =>
            apply Or.inl
            apply Or.inl
            intro assump_96
            have assump_383 : (p6 → p2) := by
              intro assump_102
              have assump_384 : (p6 ∨ p1) := by
                apply Or.inl
                exact assump_102
              let assump_107 := assump_91 assump_384
              apply False.elim assump_107
            let assump_101 := assump_90 assump_383
            apply False.elim assump_101
  apply And.intro
  intro assump_114
  cases assump_114
  case intro assump_115 assump_116 =>
    cases assump_1
    case intro assump_121 assump_122 =>
      cases assump_121
      case inl assump_123 =>
        cases assump_123
        case intro assump_125 assump_126 =>
          cases assump_125
          case inl assump_127 =>
            cases assump_122
            case intro assump_133 assump_134 =>
              have assump_385 : (p6 ∨ p1) := by
                apply Or.inl
                exact assump_115
              let assump_139 := assump_134 assump_385
              apply False.elim assump_139
          case inr assump_128 =>
            cases assump_122
            case intro assump_147 assump_148 =>
              have assump_386 : (p6 ∨ p1) := by
                apply Or.inl
                exact assump_115
              let assump_153 := assump_148 assump_386
              apply False.elim assump_153
      case inr assump_124 =>
        cases assump_124
        case inl assump_157 =>
          cases assump_122
          case intro assump_161 assump_162 =>
            have assump_387 : (p6 ∨ p1) := by
              apply Or.inl
              exact assump_115
            let assump_167 := assump_162 assump_387
            apply False.elim assump_167
        case inr assump_158 =>
          cases assump_158
          case inl assump_171 =>
            apply False.elim assump_171
          case inr assump_172 =>
            cases assump_122
            case intro assump_177 assump_178 =>
              have assump_388 : (p6 ∨ p1) := by
                apply Or.inl
                exact assump_115
              let assump_183 := assump_178 assump_388
              apply False.elim assump_183
  intro assump_187
  apply And.intro
  cases assump_1
  case intro assump_190 assump_191 =>
    cases assump_190
    case inl assump_192 =>
      cases assump_192
      case intro assump_194 assump_195 =>
        cases assump_194
        case inl assump_196 =>
          cases assump_191
          case intro assump_202 assump_203 =>
            have assump_389 : (p6 → p2) := by
              intro assump_210
              have assump_390 : (p6 ∨ p1) := by
                apply Or.inl
                exact assump_210
              let assump_214 := assump_203 assump_390
              apply False.elim assump_214
            let assump_209 := assump_202 assump_389
            apply False.elim assump_209
        case inr assump_197 =>
          cases assump_191
          case intro assump_225 assump_226 =>
            have assump_391 : (p6 ∨ p1) := by
              apply Or.inr
              exact assump_197
            let assump_231 := assump_226 assump_391
            apply False.elim assump_231
    case inr assump_193 =>
      cases assump_193
      case inl assump_235 =>
        cases assump_191
        case intro assump_239 assump_240 =>
          have assump_392 : (p6 → p2) := by
            intro assump_247
            have assump_393 : (p6 ∨ p1) := by
              apply Or.inl
              exact assump_247
            let assump_251 := assump_240 assump_393
            apply False.elim assump_251
          let assump_246 := assump_239 assump_392
          apply False.elim assump_246
      case inr assump_236 =>
        cases assump_236
        case inl assump_258 =>
          apply False.elim assump_258
        case inr assump_259 =>
          cases assump_191
          case intro assump_264 assump_265 =>
            have assump_394 : (p6 → p2) := by
              intro assump_272
              have assump_395 : (p6 ∨ p1) := by
                apply Or.inl
                exact assump_272
              let assump_276 := assump_265 assump_395
              apply False.elim assump_276
            let assump_271 := assump_264 assump_394
            apply False.elim assump_271
  cases assump_1
  case intro assump_285 assump_286 =>
    cases assump_285
    case inl assump_287 =>
      cases assump_287
      case intro assump_289 assump_290 =>
        cases assump_289
        case inl assump_291 =>
          cases assump_286
          case intro assump_297 assump_298 =>
            have assump_396 : (p6 → p2) := by
              intro assump_305
              have assump_397 : (p6 ∨ p1) := by
                apply Or.inl
                exact assump_305
              let assump_309 := assump_298 assump_397
              apply False.elim assump_309
            let assump_304 := assump_297 assump_396
            apply False.elim assump_304
        case inr assump_292 =>
          cases assump_286
          case intro assump_320 assump_321 =>
            have assump_398 : (p6 ∨ p1) := by
              apply Or.inr
              exact assump_292
            let assump_326 := assump_321 assump_398
            apply False.elim assump_326
    case inr assump_288 =>
      cases assump_288
      case inl assump_330 =>
        cases assump_286
        case intro assump_334 assump_335 =>
          have assump_399 : (p6 → p2) := by
            intro assump_342
            have assump_400 : (p6 ∨ p1) := by
              apply Or.inl
              exact assump_342
            let assump_346 := assump_335 assump_400
            apply False.elim assump_346
          let assump_341 := assump_334 assump_399
          apply False.elim assump_341
      case inr assump_331 =>
        cases assump_331
        case inl assump_353 =>
          apply False.elim assump_353
        case inr assump_354 =>
          cases assump_286
          case intro assump_359 assump_360 =>
            have assump_401 : (p6 → p2) := by
              intro assump_367
              have assump_402 : (p6 ∨ p1) := by
                apply Or.inl
                exact assump_367
              let assump_371 := assump_360 assump_402
              apply False.elim assump_371
            let assump_366 := assump_359 assump_401
            apply False.elim assump_366


variable (p5 p1 p4 p0 : Prop)
theorem file24_117968 : (((((p1 ∧ p5) → False) → False) ∧ (((p1 ∨ p4) ∨ (p4 ∧ p0)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_26 : ((p1 ∧ p5) → False) := by
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        have assump_27 : ((p1 ∨ p4) ∨ (p4 ∧ p0)) := by
          apply Or.inl
          apply Or.inl
          exact assump_11
        let assump_19 := assump_3 assump_27
        apply False.elim assump_19
    let assump_9 := assump_2 assump_26
    apply False.elim assump_9


variable (p0 p6 p2 p3 p4 : Prop)
theorem file24_118583 : ((((((p3 ∨ True) → False) → ((p3 → p6) ∨ (False ∨ False))) ∧ (((True ∨ p2) → (p4 ∨ p0)) → ((False → False) ∨ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p3 ∨ True) → False) → ((p3 → p6) ∨ (False ∨ False))) ∧ (((True ∨ p2) → (p4 ∨ p0)) → ((False → False) ∨ (p2 → False)))) := by
    apply And.intro
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_26 : (p3 ∨ True) := by
      apply Or.inl
      exact assump_8
    let assump_12 := assump_5 assump_26
    apply False.elim assump_12
    intro assump_16
    apply Or.inl
    intro assump_19
    apply False.elim assump_19
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p1 p3 p0 p2 p5 : Prop)
theorem file24_119332 : ((((((p3 → p0) ∧ (p0 → False)) → ((p2 → p0) → (p1 → False))) → False) ∧ ((((p5 → False) ∧ (True → False)) → ((p1 → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_26 : (((p5 → False) ∧ (True → False)) → ((p1 → False) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        have assump_27 : True := by
          apply True.intro
        let assump_19 := assump_14 assump_27
        apply False.elim assump_19
    let assump_8 := assump_3 assump_26
    apply False.elim assump_8


variable (p2 p3 p7 p0 p4 p5 p1 p6 : Prop)
theorem file24_120025 : (((((True ∨ p2) ∨ (p1 ∧ p3)) → False) → (((p7 → False) → False) → False)) ∨ ((((p5 ∨ p7) ∨ (p1 → True)) ∧ ((p6 ∧ p0) ∨ (p7 ∨ p6))) → (((False → p5) ∧ (p1 ∨ p2)) ∧ ((p3 ∨ p1) → (p6 → p4))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_11 : ((True ∨ p2) ∨ (p1 ∧ p3)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p1 p3 p4 p5 p0 p2 p6 p7 : Prop)
theorem file24_120507 : (((((False → False) ∧ (p1 ∧ p3)) ∧ ((p4 ∧ p5) ∨ (p7 ∨ p1))) ∧ (((p5 ∧ p4) ∧ (p5 → p4)) → False)) ∨ ((((p4 → True) → False) → ((p4 ∨ p2) → (p2 → p1))) ∨ (((p3 ∨ p5) ∨ (True ∨ p0)) → ((p5 ∧ p6) ∧ (p3 ∧ p0))))) := by
  apply Or.inr
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_5
  case inl assump_9 =>
    have assump_29 : (p4 → True) := by
      intro assump_16
      apply True.intro
    let assump_15 := assump_4 assump_29
    apply False.elim assump_15
  case inr assump_10 =>
    have assump_30 : (p4 → True) := by
      intro assump_25
      apply True.intro
    let assump_24 := assump_4 assump_30
    apply False.elim assump_24


variable (p5 p7 p0 p2 p1 p6 : Prop)
theorem file24_121236 : ((((((p2 → False) → (p5 → False)) ∨ ((p6 ∨ False) ∨ (p6 ∨ p5))) ∨ (((True → False) → (p0 → False)) → ((p0 → False) → False))) ∧ ((((p5 ∧ False) ∨ (True → False)) → ((p5 → p7) ∨ (p1 ∨ p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_151 : (((p5 ∧ False) ∨ (True → False)) → ((p5 → p7) ∨ (p1 ∨ p7))) := by
          intro assump_13
          cases assump_13
          case inl assump_14 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_17
          case inr assump_15 =>
            apply Or.inl
            intro assump_24
            have assump_152 : True := by
              apply True.intro
            let assump_28 := assump_15 assump_152
            apply False.elim assump_28
        let assump_12 := assump_3 assump_151
        apply False.elim assump_12
      case inr assump_7 =>
        cases assump_7
        case inl assump_35 =>
          cases assump_35
          case inl assump_37 =>
            have assump_153 : (((p5 ∧ False) ∨ (True → False)) → ((p5 → p7) ∨ (p1 ∨ p7))) := by
              intro assump_44
              cases assump_44
              case inl assump_45 =>
                cases assump_45
                case intro assump_47 assump_48 =>
                  apply False.elim assump_48
              case inr assump_46 =>
                apply Or.inl
                intro assump_55
                have assump_154 : True := by
                  apply True.intro
                let assump_59 := assump_46 assump_154
                apply False.elim assump_59
            let assump_43 := assump_3 assump_153
            apply False.elim assump_43
          case inr assump_38 =>
            apply False.elim assump_38
        case inr assump_36 =>
          cases assump_36
          case inl assump_68 =>
            have assump_155 : (((p5 ∧ False) ∨ (True → False)) → ((p5 → p7) ∨ (p1 ∨ p7))) := by
              intro assump_75
              cases assump_75
              case inl assump_76 =>
                cases assump_76
                case intro assump_78 assump_79 =>
                  apply False.elim assump_79
              case inr assump_77 =>
                apply Or.inl
                intro assump_86
                have assump_156 : True := by
                  apply True.intro
                let assump_90 := assump_77 assump_156
                apply False.elim assump_90
            let assump_74 := assump_3 assump_155
            apply False.elim assump_74
          case inr assump_69 =>
            have assump_157 : (((p5 ∧ False) ∨ (True → False)) → ((p5 → p7) ∨ (p1 ∨ p7))) := by
              intro assump_102
              cases assump_102
              case inl assump_103 =>
                cases assump_103
                case intro assump_105 assump_106 =>
                  apply False.elim assump_106
              case inr assump_104 =>
                apply Or.inl
                intro assump_113
                have assump_158 : True := by
                  apply True.intro
                let assump_117 := assump_104 assump_158
                apply False.elim assump_117
            let assump_101 := assump_3 assump_157
            apply False.elim assump_101
    case inr assump_5 =>
      have assump_159 : (((p5 ∧ False) ∨ (True → False)) → ((p5 → p7) ∨ (p1 ∨ p7))) := by
        intro assump_129
        cases assump_129
        case inl assump_130 =>
          cases assump_130
          case intro assump_132 assump_133 =>
            apply False.elim assump_133
        case inr assump_131 =>
          apply Or.inl
          intro assump_140
          have assump_160 : True := by
            apply True.intro
          let assump_144 := assump_131 assump_160
          apply False.elim assump_144
      let assump_128 := assump_3 assump_159
      apply False.elim assump_128


variable (p5 p3 p6 p2 p0 p7 p1 : Prop)
theorem file24_125300 : ((((((p6 ∨ p6) ∨ (p6 ∧ p3)) ∧ ((p6 ∨ False) ∨ (p0 ∨ p5))) ∧ (((p1 → False) ∧ (p2 ∨ p0)) → ((p7 → False) → (p3 → p2)))) ∧ ((((p1 → False) → (p5 ∨ p6)) ∨ ((p0 ∨ p1) → (False ∨ p0))) → False)) → False) := by
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
                have assump_163 : (((p1 → False) → (p5 ∨ p6)) ∨ ((p0 ∨ p1) → (False ∨ p0))) := by
                  apply Or.inl
                  intro assump_25
                  apply Or.inr
                  exact assump_16
                let assump_24 := assump_3 assump_163
                apply False.elim assump_24
              case inr assump_17 =>
                apply False.elim assump_17
            case inr assump_15 =>
              cases assump_15
              case inl assump_33 =>
                have assump_164 : (((p1 → False) → (p5 ∨ p6)) ∨ ((p0 ∨ p1) → (False ∨ p0))) := by
                  apply Or.inl
                  intro assump_42
                  apply Or.inr
                  exact assump_10
                let assump_41 := assump_3 assump_164
                apply False.elim assump_41
              case inr assump_34 =>
                have assump_165 : (((p1 → False) → (p5 ∨ p6)) ∨ ((p0 ∨ p1) → (False ∨ p0))) := by
                  apply Or.inl
                  intro assump_55
                  apply Or.inl
                  exact assump_34
                let assump_54 := assump_3 assump_165
                apply False.elim assump_54
          case inr assump_11 =>
            cases assump_7
            case inl assump_63 =>
              cases assump_63
              case inl assump_65 =>
                have assump_166 : (((p1 → False) → (p5 ∨ p6)) ∨ ((p0 ∨ p1) → (False ∨ p0))) := by
                  apply Or.inl
                  intro assump_74
                  apply Or.inr
                  exact assump_65
                let assump_73 := assump_3 assump_166
                apply False.elim assump_73
              case inr assump_66 =>
                apply False.elim assump_66
            case inr assump_64 =>
              cases assump_64
              case inl assump_82 =>
                have assump_167 : (((p1 → False) → (p5 ∨ p6)) ∨ ((p0 ∨ p1) → (False ∨ p0))) := by
                  apply Or.inl
                  intro assump_91
                  apply Or.inr
                  exact assump_11
                let assump_90 := assump_3 assump_167
                apply False.elim assump_90
              case inr assump_83 =>
                have assump_168 : (((p1 → False) → (p5 ∨ p6)) ∨ ((p0 ∨ p1) → (False ∨ p0))) := by
                  apply Or.inl
                  intro assump_104
                  apply Or.inl
                  exact assump_83
                let assump_103 := assump_3 assump_168
                apply False.elim assump_103
        case inr assump_9 =>
          cases assump_9
          case intro assump_110 assump_111 =>
            cases assump_7
            case inl assump_116 =>
              cases assump_116
              case inl assump_118 =>
                have assump_169 : (((p1 → False) → (p5 ∨ p6)) ∨ ((p0 ∨ p1) → (False ∨ p0))) := by
                  apply Or.inl
                  intro assump_127
                  apply Or.inr
                  exact assump_118
                let assump_126 := assump_3 assump_169
                apply False.elim assump_126
              case inr assump_119 =>
                apply False.elim assump_119
            case inr assump_117 =>
              cases assump_117
              case inl assump_135 =>
                have assump_170 : (((p1 → False) → (p5 ∨ p6)) ∨ ((p0 ∨ p1) → (False ∨ p0))) := by
                  apply Or.inl
                  intro assump_144
                  apply Or.inr
                  exact assump_110
                let assump_143 := assump_3 assump_170
                apply False.elim assump_143
              case inr assump_136 =>
                have assump_171 : (((p1 → False) → (p5 ∨ p6)) ∨ ((p0 ∨ p1) → (False ∨ p0))) := by
                  apply Or.inl
                  intro assump_157
                  apply Or.inl
                  exact assump_136
                let assump_156 := assump_3 assump_171
                apply False.elim assump_156


variable (p1 p3 p6 p5 p4 p2 p0 : Prop)
theorem file24_129957 : ((((((p6 → p4) ∧ (False ∨ p2)) ∧ ((p5 → p3) → False)) → False) ∧ ((((p4 → False) → (p1 → False)) ∨ ((True → p4) → False)) ∧ (((p2 → True) ∨ (p5 → p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_28 : ((p2 → True) ∨ (p5 → p0)) := by
          apply Or.inl
          intro assump_15
          apply True.intro
        let assump_14 := assump_7 assump_28
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_29 : ((p2 → True) ∨ (p5 → p0)) := by
          apply Or.inl
          intro assump_24
          apply True.intro
        let assump_23 := assump_7 assump_29
        apply False.elim assump_23


variable (p0 p6 p7 p5 p1 p3 : Prop)
theorem file24_130816 : ((((((p5 ∨ p3) → False) → ((p5 ∧ p7) → False)) ∨ (((p6 ∨ True) → (p1 → False)) ∨ ((p0 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p5 ∨ p3) → False) → ((p5 ∧ p7) → False)) ∨ (((p6 ∨ True) → (p1 → False)) ∨ ((p0 → False) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_23 : (p5 ∨ p3) := by
        apply Or.inl
        exact assump_7
      let assump_15 := assump_5 assump_23
      apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p1 p0 p7 : Prop)
theorem file24_131476 : ((((((True ∨ p1) → False) ∧ ((p1 → p0) ∨ (p7 → True))) → False) → False) → False) := by
  intro assump_10
  have assump_38 : ((((True ∨ p1) → False) ∧ ((p1 → p0) ∨ (p7 → True))) → False) := by
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      cases assump_16
      case inl assump_19 =>
        have assump_39 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_24 := assump_15 assump_39
        apply False.elim assump_24
      case inr assump_20 =>
        have assump_40 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_31 := assump_15 assump_40
        apply False.elim assump_31
  let assump_13 := assump_10 assump_38
  apply False.elim assump_13


variable (p7 p3 p6 p4 p2 p5 p1 p0 : Prop)
theorem file24_132305 : (((((p7 → p6) ∧ (p2 ∧ p6)) ∧ ((p1 → True) ∨ (p0 ∧ p5))) ∧ (((p3 ∧ p3) ∧ (p6 → p5)) ∨ ((True → False) → (p5 ∧ p1)))) → ((((p6 ∨ p6) ∨ (p6 ∧ True)) ∨ ((p6 → False) ∨ (p7 → p1))) → (((p7 → False) ∧ (True → p1)) → ((p2 ∨ p4) → (False → p4))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p1 p6 p2 p3 : Prop)
theorem file24_132718 : (((((False ∧ p2) ∧ (p3 ∧ p6)) → ((p1 → False) → False)) ∧ (((False ∧ False) → (p3 → p2)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : ((False ∧ False) → (p3 → p2)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        apply False.elim assump_13
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


