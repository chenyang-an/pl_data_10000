variable (p0 p4 p5 p7 p1 p6 : Prop)
theorem file30_44 : (((((True ∧ p7) ∧ (True → False)) → ((True → False) ∨ (True ∧ p1))) ∨ (((p0 → False) → (p6 ∧ p0)) ∧ ((p5 → False) ∧ (p5 ∧ p7)))) ∨ ((((p1 → False) ∧ (p4 ∨ p5)) ∨ ((p7 → p1) ∨ (p0 → False))) ∨ (((p6 ∧ p5) ∧ (False ∨ p5)) ∨ ((p6 → p6) → (p5 ∧ p0))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_12
      have assump_19 : True := by
        apply True.intro
      let assump_15 := assump_3 assump_19
      apply False.elim assump_15


variable (p6 p7 p0 p3 p4 p5 p2 p1 : Prop)
theorem file30_693 : ((((((p2 → False) → (False ∨ p6)) ∧ ((p5 → p0) → False)) ∧ (((p2 → False) ∨ (p5 ∨ p1)) → ((p5 ∨ p1) ∨ (p7 ∨ p1)))) ∧ ((((p2 ∧ p3) → (False → False)) ∧ ((p5 ∧ p0) ∨ (p0 → False))) ∧ (((p6 ∧ False) → (p5 ∧ p4)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_17
            case inl assump_20 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                have assump_68 : ((p6 ∧ False) → (p5 ∧ p4)) := by
                  intro assump_31
                  apply And.intro
                  cases assump_31
                  case intro assump_32 assump_33 =>
                    apply False.elim assump_33
                  cases assump_31
                  case intro assump_38 assump_39 =>
                    apply False.elim assump_39
                let assump_30 := assump_15 assump_68
                apply False.elim assump_30
            case inr assump_21 =>
              have assump_69 : ((p6 ∧ False) → (p5 ∧ p4)) := by
                intro assump_52
                apply And.intro
                cases assump_52
                case intro assump_53 assump_54 =>
                  apply False.elim assump_54
                cases assump_52
                case intro assump_59 assump_60 =>
                  apply False.elim assump_60
              let assump_51 := assump_15 assump_69
              apply False.elim assump_51


variable (p2 p3 p1 p6 p7 p5 p0 : Prop)
theorem file30_2452 : (((((True → False) ∧ (p0 → True)) ∧ ((p6 ∨ p3) ∨ (True → p1))) → False) ∨ ((((p7 ∨ p5) → (p3 → False)) → ((True → False) ∨ (p6 ∨ p2))) ∨ (((p3 → p1) → False) ∨ ((False → False) → (p3 ∨ p7))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          have assump_39 : True := by
            apply True.intro
          let assump_18 := assump_4 assump_39
          apply False.elim assump_18
        case inr assump_13 =>
          have assump_40 : True := by
            apply True.intro
          let assump_26 := assump_4 assump_40
          apply False.elim assump_26
      case inr assump_11 =>
        have assump_41 : True := by
          apply True.intro
        let assump_35 := assump_4 assump_41
        apply False.elim assump_35


variable (p3 p6 p1 p7 p0 p5 : Prop)
theorem file30_3452 : (((((False ∧ p3) ∧ (p6 ∨ p0)) → False) ∨ (((p6 → p7) → (p1 ∨ p5)) → ((p3 ∨ True) ∧ (False ∨ False)))) ∨ ((((p5 → False) ∨ (p1 ∨ True)) → False) → (((p3 → p7) → False) ∧ ((p7 → False) ∨ (False → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_4


variable (p4 p7 p3 p2 p1 p6 : Prop)
theorem file30_3908 : (((((True ∨ p2) → False) ∧ ((p6 ∨ p7) → False)) → (((p7 → p1) ∧ (p7 → False)) → ((p4 ∧ p2) ∧ (p2 ∧ False)))) ∧ ((((True ∨ p3) → False) → False) ∨ (((p6 ∨ p7) → False) → False))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      have assump_78 : (True ∨ p2) := by
        apply Or.inl
        apply True.intro
      let assump_16 := assump_9 assump_78
      apply False.elim assump_16
  cases assump_2
  case intro assump_20 assump_21 =>
    cases assump_1
    case intro assump_26 assump_27 =>
      have assump_79 : (True ∨ p2) := by
        apply Or.inl
        apply True.intro
      let assump_33 := assump_26 assump_79
      apply False.elim assump_33
  apply And.intro
  cases assump_2
  case intro assump_37 assump_38 =>
    cases assump_1
    case intro assump_43 assump_44 =>
      have assump_80 : (True ∨ p2) := by
        apply Or.inl
        apply True.intro
      let assump_50 := assump_43 assump_80
      apply False.elim assump_50
  cases assump_2
  case intro assump_54 assump_55 =>
    cases assump_1
    case intro assump_60 assump_61 =>
      have assump_81 : (True ∨ p2) := by
        apply Or.inl
        apply True.intro
      let assump_67 := assump_60 assump_81
      apply False.elim assump_67
  apply Or.inl
  intro assump_71
  have assump_82 : (True ∨ p3) := by
    apply Or.inl
    apply True.intro
  let assump_74 := assump_71 assump_82
  apply False.elim assump_74


variable (p6 : Prop)
theorem file30_5507 : (((((p6 → True) → False) → False) → False) → False) := by
  intro assump_1
  have assump_16 : (((p6 → True) → False) → False) := by
    intro assump_5
    have assump_17 : (p6 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p5 p4 p7 p6 p3 p2 p0 p1 : Prop)
theorem file30_5941 : (((((True ∨ p6) ∨ (p4 → p0)) → False) → (((False → True) → (p5 → p6)) ∨ ((True → False) ∧ (p1 → p4)))) → ((((p4 ∧ p3) → (p2 → p4)) ∧ ((p2 ∧ False) → False)) ∨ (((p7 → False) ∧ (p4 ∨ True)) → False))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    exact assump_8
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    apply False.elim assump_16


variable (p2 p4 p6 p3 p5 p7 p1 p0 : Prop)
theorem file30_6470 : (((((p7 → p0) ∨ (p2 → True)) → ((p3 ∧ p1) ∨ (p3 → True))) → (((p6 ∨ p4) → False) ∧ ((False ∧ p5) ∧ (p0 → p6)))) → False) := by
  intro assump_1
  have assump_21 : (((p7 → p0) ∨ (p2 → True)) → ((p3 ∧ p1) ∨ (p3 → True))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inr
      intro assump_10
      apply True.intro
    case inr assump_7 =>
      apply Or.inr
      intro assump_13
      apply True.intro
  let assump_4 := assump_1 assump_21
  let assump_14 := And.right assump_4
  let assump_16 := And.left assump_14
  let assump_17 := And.left assump_16
  apply False.elim assump_17


variable (p7 p2 p5 p3 p1 p4 : Prop)
theorem file30_7151 : (((((p3 → p1) → False) ∧ ((p4 ∧ p1) → (p4 ∨ p2))) → (((p5 ∨ True) ∨ (p4 → False)) ∨ ((p3 → False) ∧ (p7 ∧ p1)))) ∧ ((((p1 ∧ False) → (False ∧ p1)) → False) → (((p7 → False) → (p5 ∨ p5)) → False))) := by
  apply And.intro
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  intro assump_12
  intro assump_13
  have assump_35 : ((p1 ∧ False) → (False ∧ p1)) := by
    intro assump_19
    apply And.intro
    cases assump_19
    case intro assump_20 assump_21 =>
      apply False.elim assump_21
    cases assump_19
    case intro assump_26 assump_27 =>
      apply False.elim assump_27
  let assump_18 := assump_12 assump_35
  apply False.elim assump_18


variable (p6 p7 p2 p1 p0 p5 : Prop)
theorem file30_7953 : (((((p1 ∨ True) ∧ (p7 ∧ p6)) → ((p7 → p7) ∨ (p2 ∧ p2))) → False) → ((((p5 ∧ p1) → False) ∧ ((p2 → False) ∨ (p2 → p6))) ∧ (((p0 → False) → (p1 → False)) → ((p0 → False) ∨ (p1 ∨ p0))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_119 : (((p1 ∨ True) ∧ (p7 ∧ p6)) → ((p7 → p7) ∨ (p2 ∧ p2))) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        cases assump_13
        case inl assump_15 =>
          cases assump_14
          case intro assump_19 assump_20 =>
            apply Or.inl
            intro assump_25
            exact assump_25
        case inr assump_16 =>
          cases assump_14
          case intro assump_30 assump_31 =>
            apply Or.inl
            intro assump_36
            exact assump_36
    let assump_11 := assump_1 assump_119
    apply False.elim assump_11
  apply Or.inl
  intro assump_44
  have assump_120 : (((p1 ∨ True) ∧ (p7 ∧ p6)) → ((p7 → p7) ∨ (p2 ∧ p2))) := by
    intro assump_49
    cases assump_49
    case intro assump_50 assump_51 =>
      cases assump_50
      case inl assump_52 =>
        cases assump_51
        case intro assump_56 assump_57 =>
          apply Or.inl
          intro assump_62
          exact assump_62
      case inr assump_53 =>
        cases assump_51
        case intro assump_67 assump_68 =>
          apply Or.inl
          intro assump_73
          exact assump_73
  let assump_48 := assump_1 assump_120
  apply False.elim assump_48
  intro assump_79
  apply Or.inl
  intro assump_84
  have assump_121 : (((p1 ∨ True) ∧ (p7 ∧ p6)) → ((p7 → p7) ∨ (p2 ∧ p2))) := by
    intro assump_89
    cases assump_89
    case intro assump_90 assump_91 =>
      cases assump_90
      case inl assump_92 =>
        cases assump_91
        case intro assump_96 assump_97 =>
          apply Or.inl
          intro assump_102
          exact assump_102
      case inr assump_93 =>
        cases assump_91
        case intro assump_107 assump_108 =>
          apply Or.inl
          intro assump_113
          exact assump_113
  let assump_88 := assump_1 assump_121
  apply False.elim assump_88


variable (p4 p7 p5 p3 p1 p2 p0 p6 : Prop)
theorem file30_10216 : (((((p3 ∨ p7) → False) → False) → (((p3 → p2) → (False ∨ True)) ∨ ((p3 ∨ p5) ∧ (p2 ∨ p1)))) ∨ ((((p7 ∧ p6) ∨ (p6 → False)) ∨ ((p7 → False) → False)) → (((p0 ∧ p4) → False) ∨ ((p3 → p1) ∨ (p4 → True))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inr
  apply True.intro


variable (p1 p0 p4 p6 p5 p2 : Prop)
theorem file30_10583 : ((((((p6 → False) → (p1 → False)) → ((p4 ∧ p2) ∧ (p5 → True))) ∧ (((True → False) ∨ (p5 ∧ False)) → False)) ∧ ((((p0 ∨ False) → (p1 ∨ True)) ∧ ((True → False) → (p2 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_33 : (((p0 ∨ False) → (p1 ∨ True)) ∧ ((True → False) → (p2 → False))) := by
        apply And.intro
        intro assump_13
        cases assump_13
        case inl assump_14 =>
          apply Or.inr
          apply True.intro
        case inr assump_15 =>
          apply False.elim assump_15
        intro assump_20
        intro assump_21
        have assump_34 : True := by
          apply True.intro
        let assump_26 := assump_20 assump_34
        apply False.elim assump_26
      let assump_12 := assump_3 assump_33
      apply False.elim assump_12


variable (p0 p7 p3 p5 p1 p6 : Prop)
theorem file30_11546 : ((((((True ∨ p6) → False) ∧ ((p1 ∧ p0) → False)) → (((p7 → p0) ∧ (True → p3)) ∨ ((p5 ∧ p6) ∨ (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((True ∨ p6) → False) ∧ ((p1 ∧ p0) → False)) → (((p7 → p0) ∧ (True → p3)) ∨ ((p5 ∧ p6) ∨ (p0 → False)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply And.intro
      intro assump_12
      have assump_33 : (True ∨ p6) := by
        apply Or.inl
        apply True.intro
      let assump_17 := assump_6 assump_33
      apply False.elim assump_17
      intro assump_21
      have assump_34 : (True ∨ p6) := by
        apply Or.inl
        apply True.intro
      let assump_25 := assump_6 assump_34
      apply False.elim assump_25
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p1 p7 p2 p3 : Prop)
theorem file30_12430 : (((((p7 → False) ∧ (p3 ∨ p2)) → ((p3 ∧ False) → False)) → (((p1 ∧ False) ∨ (p1 → True)) → False)) → False) := by
  intro assump_1
  have assump_18 : (((p7 → False) ∧ (p3 ∨ p2)) → ((p3 ∧ False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  have assump_19 : ((p1 ∧ False) ∨ (p1 → True)) := by
    apply Or.inr
    intro assump_14
    apply True.intro
  let assump_13 := assump_4 assump_19
  apply False.elim assump_13


variable (p4 p7 p1 p0 p3 p2 p6 : Prop)
theorem file30_13043 : (((((p0 → False) ∧ (p2 ∨ p4)) → False) ∧ (((p2 → False) → (p6 → False)) ∧ ((p6 → False) ∨ (True ∧ False)))) → ((((p6 ∧ p4) → (p3 ∨ p1)) ∨ ((p6 → p7) → False)) ∨ (((p7 → False) ∧ (p4 → False)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inl
        apply Or.inl
        intro assump_14
        cases assump_14
        case intro assump_15 assump_16 =>
          have assump_33 : p6 := by
            exact assump_15
          let assump_23 := assump_10 assump_33
          apply False.elim assump_23
      case inr assump_11 =>
        cases assump_11
        case intro assump_27 assump_28 =>
          apply False.elim assump_28


variable (p5 p4 p2 p3 p6 p1 p7 p0 : Prop)
theorem file30_13901 : (((((p4 ∨ False) → False) ∨ ((p2 ∨ p7) ∧ (p7 ∧ p2))) → (((p6 → p3) → (False → p2)) ∨ ((p5 ∧ True) ∨ (p0 ∨ p4)))) ∨ ((((True ∧ p4) ∧ (p5 → p3)) ∨ ((p6 → p1) → (True ∨ p6))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  case inr assump_3 =>
    cases assump_3
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_11
        case intro assump_16 assump_17 =>
          apply Or.inl
          intro assump_22
          intro assump_23
          apply False.elim assump_23
      case inr assump_13 =>
        cases assump_11
        case intro assump_28 assump_29 =>
          apply Or.inl
          intro assump_34
          intro assump_35
          apply False.elim assump_35


variable (p0 p4 p6 p1 p3 : Prop)
theorem file30_14817 : ((((((p6 → False) ∧ (p0 → False)) ∨ ((p4 ∧ p3) ∨ (p3 → p1))) → (((p3 ∧ True) → False) → ((p1 ∧ p4) ∨ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_39 : ((((p6 → False) ∧ (p0 → False)) ∨ ((p4 ∧ p3) ∨ (p3 → p1))) → (((p3 ∧ True) → False) → ((p1 ∧ p4) ∨ (False → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply Or.inr
        intro assump_17
        apply False.elim assump_17
    case inr assump_10 =>
      cases assump_10
      case inl assump_20 =>
        cases assump_20
        case intro assump_22 assump_23 =>
          apply Or.inr
          intro assump_28
          apply False.elim assump_28
      case inr assump_21 =>
        apply Or.inr
        intro assump_33
        apply False.elim assump_33
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p5 p2 p3 p0 p6 p4 p7 p1 : Prop)
theorem file30_15811 : (((((p1 → False) → False) → False) ∧ (((p3 → False) → (p6 ∨ p0)) → False)) → ((((p4 ∨ p5) → (True ∧ p3)) ∨ ((p4 → False) → (p7 → p5))) → (((p2 ∧ False) → False) ∨ ((p2 ∨ p3) → (p3 ∨ p6))))) := by
  intro assump_9
  intro assump_10
  cases assump_10
  case inl assump_11 =>
    cases assump_9
    case intro assump_15 assump_16 =>
      apply Or.inl
      intro assump_21
      cases assump_21
      case intro assump_22 assump_23 =>
        apply False.elim assump_23
  case inr assump_12 =>
    cases assump_9
    case intro assump_30 assump_31 =>
      apply Or.inl
      intro assump_36
      cases assump_36
      case intro assump_37 assump_38 =>
        apply False.elim assump_38


variable (p3 p7 p5 p6 p1 p0 p4 : Prop)
theorem file30_16561 : (((((p3 ∧ p1) → (True ∨ p5)) ∨ ((p7 ∨ p1) ∨ (p3 → False))) → False) → ((((p0 ∨ p3) ∨ (p1 ∨ True)) ∨ ((p7 → False) → False)) ∨ (((p3 ∨ p4) ∨ (p0 → p6)) ∨ ((p3 → False) ∧ (p4 ∧ True))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inr
  apply True.intro


variable (p2 p6 p4 p5 p1 p3 p0 p7 : Prop)
theorem file30_16914 : (((((False → p2) ∧ (p5 → False)) → ((p5 → p5) ∨ (p3 → p1))) → False) → ((((True ∧ p2) ∨ (p5 → False)) → ((p4 ∨ p7) → (True ∨ p0))) ∨ (((p6 → True) → (p3 → False)) ∧ ((p0 → False) ∨ (True → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_4
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply Or.inl
        apply True.intro
    case inr assump_11 =>
      apply Or.inl
      apply True.intro
  case inr assump_7 =>
    cases assump_4
    case inl assump_22 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        apply Or.inl
        apply True.intro
    case inr assump_23 =>
      apply Or.inl
      apply True.intro


variable (p3 p6 p0 p2 p5 p4 p7 : Prop)
theorem file30_17754 : ((((((p0 → False) ∨ (True → False)) → ((p2 → p5) → False)) ∧ (((True → False) ∧ (p4 ∨ p4)) ∨ ((False ∧ p7) → (p7 ∧ p6)))) ∧ ((((p5 → p3) → False) → ((p3 ∨ p3) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case inl assump_14 =>
            have assump_118 : (((p5 → p3) → False) → ((p3 ∨ p3) → False)) := by
              intro assump_21
              intro assump_22
              cases assump_22
              case inl assump_23 =>
                have assump_119 : (p5 → p3) := by
                  intro assump_30
                  exact assump_23
                let assump_29 := assump_21 assump_119
                apply False.elim assump_29
              case inr assump_24 =>
                have assump_120 : (p5 → p3) := by
                  intro assump_41
                  exact assump_24
                let assump_40 := assump_21 assump_120
                apply False.elim assump_40
            let assump_20 := assump_3 assump_118
            apply False.elim assump_20
          case inr assump_15 =>
            have assump_121 : (((p5 → p3) → False) → ((p3 ∨ p3) → False)) := by
              intro assump_55
              intro assump_56
              cases assump_56
              case inl assump_57 =>
                have assump_122 : (p5 → p3) := by
                  intro assump_64
                  exact assump_57
                let assump_63 := assump_55 assump_122
                apply False.elim assump_63
              case inr assump_58 =>
                have assump_123 : (p5 → p3) := by
                  intro assump_75
                  exact assump_58
                let assump_74 := assump_55 assump_123
                apply False.elim assump_74
            let assump_54 := assump_3 assump_121
            apply False.elim assump_54
      case inr assump_9 =>
        have assump_124 : (((p5 → p3) → False) → ((p3 ∨ p3) → False)) := by
          intro assump_89
          intro assump_90
          cases assump_90
          case inl assump_91 =>
            have assump_125 : (p5 → p3) := by
              intro assump_98
              exact assump_91
            let assump_97 := assump_89 assump_125
            apply False.elim assump_97
          case inr assump_92 =>
            have assump_126 : (p5 → p3) := by
              intro assump_109
              exact assump_92
            let assump_108 := assump_89 assump_126
            apply False.elim assump_108
        let assump_88 := assump_3 assump_124
        apply False.elim assump_88


variable (p0 p6 p7 p5 p1 p2 p4 : Prop)
theorem file30_20575 : (((((p6 ∧ p7) ∨ (p7 → False)) → False) ∧ (((p0 ∧ p4) ∧ (p1 ∧ p0)) ∧ ((p4 → False) ∨ (p1 ∧ False)))) → ((((p7 ∨ p2) ∨ (p5 → p4)) → False) → (((p0 → False) ∨ (p1 → True)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            cases assump_17
            case intro assump_24 assump_25 =>
              cases assump_15
              case inl assump_30 =>
                have assump_82 : p4 := by
                  exact assump_19
                let assump_34 := assump_30 assump_82
                apply False.elim assump_34
              case inr assump_31 =>
                cases assump_31
                case intro assump_38 assump_39 =>
                  apply False.elim assump_39
  case inr assump_5 =>
    cases assump_1
    case intro assump_48 assump_49 =>
      cases assump_49
      case intro assump_52 assump_53 =>
        cases assump_52
        case intro assump_54 assump_55 =>
          cases assump_54
          case intro assump_56 assump_57 =>
            cases assump_55
            case intro assump_62 assump_63 =>
              cases assump_53
              case inl assump_68 =>
                have assump_83 : p4 := by
                  exact assump_57
                let assump_72 := assump_68 assump_83
                apply False.elim assump_72
              case inr assump_69 =>
                cases assump_69
                case intro assump_76 assump_77 =>
                  apply False.elim assump_77


variable (p4 : Prop)
theorem file30_22380 : ((((((False → False) ∧ (p4 → True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((False → False) ∧ (p4 → True)) → False) → False) := by
    intro assump_5
    have assump_20 : ((False → False) ∧ (p4 → True)) := by
      apply And.intro
      intro assump_9
      apply False.elim assump_9
      intro assump_12
      apply True.intro
    let assump_8 := assump_5 assump_20
    apply False.elim assump_8
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p4 p7 p6 p0 p5 p1 : Prop)
theorem file30_22944 : (((((p4 ∨ True) → (False → False)) ∨ ((p7 → False) ∧ (p1 → p5))) ∧ (((p1 → p1) ∨ (p0 ∧ p6)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_32 : ((p1 → p1) ∨ (p0 ∧ p6)) := by
        apply Or.inl
        intro assump_11
        exact assump_11
      let assump_10 := assump_3 assump_32
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_17 assump_18 =>
        have assump_33 : ((p1 → p1) ∨ (p0 ∧ p6)) := by
          apply Or.inl
          intro assump_26
          exact assump_26
        let assump_25 := assump_3 assump_33
        apply False.elim assump_25


variable (p6 p1 p3 p4 p5 p0 : Prop)
theorem file30_23725 : ((((((p6 → p6) → False) ∨ ((p6 ∨ p6) → False)) ∧ (((True → p0) ∧ (p4 → False)) → ((p3 → False) ∧ (p1 ∧ p0)))) ∧ ((((False → False) → False) → ((p1 → False) ∨ (p1 ∧ p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        have assump_56 : (((False → False) → False) → ((p1 → False) ∨ (p1 ∧ p5))) := by
          intro assump_15
          apply Or.inl
          intro assump_18
          have assump_57 : (False → False) := by
            intro assump_23
            apply False.elim assump_23
          let assump_22 := assump_15 assump_57
          apply False.elim assump_22
        let assump_14 := assump_3 assump_56
        apply False.elim assump_14
      case inr assump_7 =>
        have assump_58 : (((False → False) → False) → ((p1 → False) ∨ (p1 ∧ p5))) := by
          intro assump_39
          apply Or.inl
          intro assump_42
          have assump_59 : (False → False) := by
            intro assump_47
            apply False.elim assump_47
          let assump_46 := assump_39 assump_59
          apply False.elim assump_46
        let assump_38 := assump_3 assump_58
        apply False.elim assump_38


variable (p0 p5 p7 : Prop)
theorem file30_25053 : (((((p0 → True) → False) → ((p5 ∨ p7) ∨ (p0 → False))) → False) → False) := by
  intro assump_1
  have assump_20 : (((p0 → True) → False) → ((p5 ∨ p7) ∨ (p0 → False))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    have assump_21 : (p0 → True) := by
      intro assump_13
      apply True.intro
    let assump_12 := assump_5 assump_21
    apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p1 p6 p3 p2 p5 p7 : Prop)
theorem file30_25562 : (((((True ∨ p7) ∨ (p3 → False)) ∨ ((p7 ∧ p6) → False)) ∨ (((p6 ∨ p5) → False) ∨ ((p1 → p3) → False))) ∨ ((((False ∨ True) ∧ (p5 → p3)) → False) ∧ (((p2 → False) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p7 p6 p3 p0 : Prop)
theorem file30_25897 : (((((False ∨ p7) ∨ (False ∨ p0)) ∨ ((p0 ∧ p6) → (p3 → p3))) → False) → False) := by
  intro assump_1
  have assump_18 : (((False ∨ p7) ∨ (False ∨ p0)) ∨ ((p0 ∧ p6) → (p3 → p3))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_6
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p2 p3 p0 p4 p7 : Prop)
theorem file30_26338 : ((((((p0 → p1) → False) → ((p2 ∧ p7) ∧ (False ∨ p0))) ∨ (((p7 ∧ p4) → False) ∧ ((True ∧ p0) → (False → False)))) ∧ ((((p0 → False) ∧ (False ∧ p3)) → ((p2 ∧ p2) ∧ (p0 → p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_82 : (((p0 → False) ∧ (False ∧ p3)) → ((p2 ∧ p2) ∧ (p0 → p1))) := by
        intro assump_11
        apply And.intro
        apply And.intro
        cases assump_11
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
        cases assump_11
        case intro assump_20 assump_21 =>
          cases assump_21
          case intro assump_24 assump_25 =>
            apply False.elim assump_24
        intro assump_28
        cases assump_11
        case intro assump_31 assump_32 =>
          cases assump_32
          case intro assump_35 assump_36 =>
            apply False.elim assump_35
      let assump_10 := assump_3 assump_82
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_42 assump_43 =>
        have assump_83 : (((p0 → False) ∧ (False ∧ p3)) → ((p2 ∧ p2) ∧ (p0 → p1))) := by
          intro assump_51
          apply And.intro
          apply And.intro
          cases assump_51
          case intro assump_52 assump_53 =>
            cases assump_53
            case intro assump_56 assump_57 =>
              apply False.elim assump_56
          cases assump_51
          case intro assump_60 assump_61 =>
            cases assump_61
            case intro assump_64 assump_65 =>
              apply False.elim assump_64
          intro assump_68
          cases assump_51
          case intro assump_71 assump_72 =>
            cases assump_72
            case intro assump_75 assump_76 =>
              apply False.elim assump_75
        let assump_50 := assump_3 assump_83
        apply False.elim assump_50


variable (p3 p0 p1 p6 p4 : Prop)
theorem file30_28402 : (((((p4 ∨ p1) ∨ (p4 → False)) → False) → (((p0 ∨ p4) → (False ∧ p4)) → False)) ∨ ((((True → p6) ∧ (p6 ∧ False)) ∧ ((p4 → p6) ∨ (p3 ∨ False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_19 : ((p4 ∨ p1) ∨ (p4 → False)) := by
    apply Or.inr
    intro assump_8
    have assump_20 : ((p4 ∨ p1) ∨ (p4 → False)) := by
      apply Or.inl
      apply Or.inl
      exact assump_8
    let assump_12 := assump_1 assump_20
    apply False.elim assump_12
  let assump_7 := assump_1 assump_19
  apply False.elim assump_7


variable (p0 p5 p1 p4 p6 p3 p2 : Prop)
theorem file30_29009 : (((((p6 → False) → False) → False) → (((p1 ∧ p6) ∧ (False → True)) → False)) ∨ ((((p5 → False) → (p2 ∧ p5)) → ((p1 ∨ p0) ∨ (p1 ∨ p3))) ∨ (((p0 ∧ p4) ∧ (p0 → False)) → ((p0 ∨ False) ∨ (p0 ∨ p0))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      have assump_26 : ((p6 → False) → False) := by
        intro assump_16
        have assump_27 : p6 := by
          exact assump_6
        let assump_19 := assump_16 assump_27
        apply False.elim assump_19
      let assump_15 := assump_1 assump_26
      apply False.elim assump_15


variable (p0 p4 p7 p2 p5 p3 p6 p1 : Prop)
theorem file30_29723 : (((((p4 ∧ False) ∧ (p0 → False)) → ((p3 → False) → (p1 ∨ p0))) ∨ (((p2 ∨ p7) ∧ (p5 ∨ p2)) → False)) ∨ ((((p0 → False) → (p6 → p2)) → ((p0 → p6) → (p3 → p6))) ∧ (((p7 → False) ∨ (p5 → False)) → ((p1 ∨ p7) → (p3 → p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply False.elim assump_8


variable (p0 p7 p5 p3 p1 p4 p6 p2 : Prop)
theorem file30_30217 : (((((p5 → False) → False) ∧ ((p6 → p7) ∧ (True → False))) → False) → ((((True → False) → (p5 ∨ p6)) ∨ ((p0 → p1) → (p3 ∧ False))) ∨ (((p4 ∧ True) → (p0 ∨ p0)) → ((p5 ∨ p4) ∧ (p2 → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_11 : True := by
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p6 p4 p2 p0 p1 p3 p5 p7 : Prop)
theorem file30_30660 : (((((p2 → p4) ∨ (p3 ∨ p5)) → ((True ∨ p1) ∨ (p5 ∧ p7))) ∨ (((p7 ∨ p0) ∨ (p6 → False)) ∨ ((p3 ∨ False) ∨ (p4 ∧ p1)))) ∨ ((((True → False) → False) ∧ ((p5 ∨ p5) ∨ (True ∨ p2))) ∨ (((p0 ∧ p3) ∨ (p7 ∨ p0)) ∧ ((p2 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p1 p6 p5 p7 p0 p4 p2 p3 : Prop)
theorem file30_31318 : (((((False → p3) ∨ (p5 → True)) → ((p6 ∨ p2) ∨ (p4 → p1))) → (((p0 → False) ∧ (p3 ∧ False)) → ((p6 → False) → False))) ∨ ((((p3 → False) ∨ (p7 ∧ p1)) ∨ ((False ∧ False) ∧ (p1 → False))) → False)) := by
  apply Or.inl
  intro assump_78
  intro assump_79
  intro assump_80
  cases assump_79
  case intro assump_83 assump_84 =>
    cases assump_84
    case intro assump_87 assump_88 =>
      apply False.elim assump_88


variable (p3 p5 p2 p4 p1 p6 : Prop)
theorem file30_31794 : (((((p1 → False) ∧ (p6 → p3)) → ((p4 → p5) → False)) ∧ (((True ∧ p3) ∧ (p2 → False)) → False)) → ((((p1 → p1) → False) → False) ∨ (((p1 ∧ p6) → False) → ((p6 → p6) → (p3 ∨ True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    have assump_18 : (p1 → p1) := by
      intro assump_12
      exact assump_12
    let assump_11 := assump_8 assump_18
    apply False.elim assump_11


variable (p5 p0 p2 p7 : Prop)
theorem file30_32292 : (((((True ∨ p7) ∨ (p0 → p5)) ∨ ((p5 ∧ p2) ∧ (p7 → False))) → False) → ((((False → False) ∧ (p7 → p0)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_11 : (((True ∨ p7) ∨ (p0 → p5)) ∨ ((p5 ∧ p2) ∧ (p7 → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p5 p0 p2 p6 p4 p1 p7 : Prop)
theorem file30_32735 : (((((False → False) → (p5 → p0)) ∨ ((False → p6) ∧ (False → False))) → (((p1 → True) ∧ (True → False)) → ((p6 ∨ p1) ∨ (p6 ∨ p4)))) ∨ ((((p0 → p2) → False) → False) ∧ (((p4 → False) → (p1 → False)) ∨ ((True → p7) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case inl assump_9 =>
      have assump_34 : True := by
        apply True.intro
      let assump_18 := assump_4 assump_34
      apply False.elim assump_18
    case inr assump_10 =>
      cases assump_10
      case intro assump_22 assump_23 =>
        have assump_35 : True := by
          apply True.intro
        let assump_30 := assump_4 assump_35
        apply False.elim assump_30


variable (p0 p5 p1 p3 p2 p7 : Prop)
theorem file30_33533 : (((((p1 → False) → False) ∧ ((p0 ∧ p0) ∧ (p0 ∧ p7))) ∧ (((True ∧ p1) → False) ∧ ((p5 → False) → (False → p7)))) → ((((p1 ∨ p3) → False) → ((p2 ∧ p1) ∨ (p0 ∧ p0))) ∨ (((p7 ∨ p7) ∨ (p5 → p0)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            cases assump_3
            case intro assump_22 assump_23 =>
              apply Or.inl
              intro assump_28
              apply Or.inr
              apply And.intro
              exact assump_16
              exact assump_16


variable (p1 p5 p7 p3 p0 p4 p6 p2 : Prop)
theorem file30_34369 : (((((p5 → p0) → (False → False)) → ((p2 ∧ p2) → (p4 → True))) → (((p2 → False) ∧ (True → False)) → ((False → p3) ∨ (True ∧ p3)))) ∨ ((((p0 ∨ p6) → False) ∨ ((p1 ∨ p3) → False)) ∧ (((p1 → False) ∨ (p7 ∧ p0)) ∨ ((p6 ∨ p3) → (p2 ∨ False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inl
    intro assump_11
    apply False.elim assump_11


variable (p0 p1 p2 p3 p6 p5 p4 p7 : Prop)
theorem file30_34848 : ((((((p2 → False) ∨ (True → p7)) ∨ ((p1 → p7) ∨ (p1 ∨ True))) → (((p4 → False) ∨ (True ∧ False)) → ((p6 ∧ p7) ∧ (p2 → False)))) ∧ ((((p5 ∧ True) ∨ (p6 ∧ p0)) → ((False → False) ∨ (p3 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_33 : (((p5 ∧ True) ∨ (p6 ∧ p0)) → ((False → False) ∨ (p3 → False))) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_18
          apply False.elim assump_18
      case inr assump_11 =>
        cases assump_11
        case intro assump_21 assump_22 =>
          apply Or.inl
          intro assump_27
          apply False.elim assump_27
    let assump_8 := assump_3 assump_33
    apply False.elim assump_8


variable (p1 p4 p6 p5 p3 p0 p2 : Prop)
theorem file30_35759 : (((((p4 → p4) → False) ∧ ((False ∧ p5) → False)) → (((p2 ∧ p0) → (p3 → True)) ∧ ((True ∨ False) ∧ (False → False)))) ∨ ((((p1 ∧ p5) → (p6 ∧ p1)) ∨ ((p5 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  apply True.intro
  apply And.intro
  cases assump_1
  case intro assump_4 assump_5 =>
    apply Or.inl
    apply True.intro
  intro assump_10
  apply False.elim assump_10


variable (p3 p0 p5 p7 p6 p4 : Prop)
theorem file30_36263 : (((((False ∧ p5) ∧ (p3 → p4)) ∧ ((True → p7) ∧ (p0 → p0))) ∧ (((p5 ∨ p6) ∧ (p6 ∧ p5)) → ((True ∨ p7) ∨ (p5 ∧ True)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_8


variable (p3 p4 p5 p6 p1 p7 p2 : Prop)
theorem file30_36740 : ((((((p1 ∧ p4) ∨ (p7 ∧ p6)) ∧ ((True ∨ p2) → False)) → (((p5 → p3) ∨ (False ∧ p6)) → ((p2 ∧ True) → (p1 ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_91 : ((((p1 ∧ p4) ∨ (p7 ∧ p6)) ∧ ((True ∨ p2) → False)) → (((p5 → p3) ∨ (False ∧ p6)) → ((p2 ∧ True) → (p1 ∧ p3)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply And.intro
    cases assump_7
    case intro assump_8 assump_9 =>
      cases assump_6
      case inl assump_14 =>
        cases assump_5
        case intro assump_18 assump_19 =>
          cases assump_18
          case inl assump_20 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              exact assump_22
          case inr assump_21 =>
            cases assump_21
            case intro assump_30 assump_31 =>
              have assump_92 : (True ∨ p2) := by
                apply Or.inl
                apply True.intro
              let assump_38 := assump_19 assump_92
              apply False.elim assump_38
      case inr assump_15 =>
        cases assump_15
        case intro assump_42 assump_43 =>
          apply False.elim assump_42
    cases assump_7
    case intro assump_46 assump_47 =>
      cases assump_6
      case inl assump_52 =>
        cases assump_5
        case intro assump_56 assump_57 =>
          cases assump_56
          case inl assump_58 =>
            cases assump_58
            case intro assump_60 assump_61 =>
              have assump_93 : (True ∨ p2) := by
                apply Or.inl
                apply True.intro
              let assump_68 := assump_57 assump_93
              apply False.elim assump_68
          case inr assump_59 =>
            cases assump_59
            case intro assump_72 assump_73 =>
              have assump_94 : (True ∨ p2) := by
                apply Or.inl
                apply True.intro
              let assump_80 := assump_57 assump_94
              apply False.elim assump_80
      case inr assump_53 =>
        cases assump_53
        case intro assump_84 assump_85 =>
          apply False.elim assump_84
  let assump_4 := assump_1 assump_91
  apply False.elim assump_4


variable (p0 p7 p5 p2 p1 p3 p6 p4 : Prop)
theorem file30_38955 : (((((p5 ∧ p6) ∧ (p0 ∧ p2)) → ((p0 ∨ p4) ∧ (p4 ∨ p6))) ∨ (((p2 → p3) ∧ (p0 → p2)) ∨ ((False → False) ∧ (p7 ∧ p1)))) ∨ ((((p7 → False) → False) ∧ ((p0 ∨ p6) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        apply Or.inl
        exact assump_10
  cases assump_1
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_17
      case intro assump_24 assump_25 =>
        apply Or.inr
        exact assump_19


variable (p0 p6 p5 p1 p2 p3 : Prop)
theorem file30_39691 : (((((p0 ∧ True) → (True → p2)) → False) ∧ (((p2 → False) ∨ (p5 → False)) ∧ ((p1 ∧ False) ∧ (p6 → False)))) → ((((p0 ∨ p1) → False) → ((True ∨ p3) ∨ (p3 ∧ p3))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            apply False.elim assump_18
      case inr assump_12 =>
        cases assump_10
        case intro assump_25 assump_26 =>
          cases assump_25
          case intro assump_27 assump_28 =>
            apply False.elim assump_28


variable (p0 p3 p7 p4 p2 p5 : Prop)
theorem file30_40495 : ((((((p3 ∨ True) ∨ (p5 → False)) ∨ ((p3 ∨ p3) ∨ (p7 ∨ True))) → (((p0 → True) ∨ (False ∨ p7)) → ((p0 → True) ∨ (p4 → p2)))) → False) → False) := by
  intro assump_1
  have assump_86 : ((((p3 ∨ True) ∨ (p5 → False)) ∨ ((p3 ∨ p3) ∨ (p7 ∨ True))) → (((p0 → True) ∨ (False ∨ p7)) → ((p0 → True) ∨ (p4 → p2)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_13
          case inl assump_15 =>
            apply Or.inl
            intro assump_19
            apply True.intro
          case inr assump_16 =>
            apply Or.inl
            intro assump_22
            apply True.intro
        case inr assump_14 =>
          apply Or.inl
          intro assump_25
          apply True.intro
      case inr assump_12 =>
        cases assump_12
        case inl assump_26 =>
          cases assump_26
          case inl assump_28 =>
            apply Or.inl
            intro assump_32
            apply True.intro
          case inr assump_29 =>
            apply Or.inl
            intro assump_35
            apply True.intro
        case inr assump_27 =>
          cases assump_27
          case inl assump_36 =>
            apply Or.inl
            intro assump_40
            apply True.intro
          case inr assump_37 =>
            apply Or.inl
            intro assump_43
            apply True.intro
    case inr assump_8 =>
      cases assump_8
      case inl assump_44 =>
        apply False.elim assump_44
      case inr assump_45 =>
        cases assump_5
        case inl assump_50 =>
          cases assump_50
          case inl assump_52 =>
            cases assump_52
            case inl assump_54 =>
              apply Or.inl
              intro assump_58
              apply True.intro
            case inr assump_55 =>
              apply Or.inl
              intro assump_61
              apply True.intro
          case inr assump_53 =>
            apply Or.inl
            intro assump_64
            apply True.intro
        case inr assump_51 =>
          cases assump_51
          case inl assump_65 =>
            cases assump_65
            case inl assump_67 =>
              apply Or.inl
              intro assump_71
              apply True.intro
            case inr assump_68 =>
              apply Or.inl
              intro assump_74
              apply True.intro
          case inr assump_66 =>
            cases assump_66
            case inl assump_75 =>
              apply Or.inl
              intro assump_79
              apply True.intro
            case inr assump_76 =>
              apply Or.inl
              intro assump_82
              apply True.intro
  let assump_4 := assump_1 assump_86
  apply False.elim assump_4


variable (p5 p0 p3 p4 : Prop)
theorem file30_43389 : ((((((p0 → p4) ∨ (p4 ∨ p5)) ∧ ((p3 → False) ∧ (p5 ∧ p3))) → False) → False) → False) := by
  intro assump_1
  have assump_69 : ((((p0 → p4) ∨ (p4 ∨ p5)) ∧ ((p3 → False) ∧ (p5 ∧ p3))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            have assump_70 : p3 := by
              exact assump_17
            let assump_24 := assump_12 assump_70
            apply False.elim assump_24
      case inr assump_9 =>
        cases assump_9
        case inl assump_28 =>
          cases assump_7
          case intro assump_32 assump_33 =>
            cases assump_33
            case intro assump_36 assump_37 =>
              have assump_71 : p3 := by
                exact assump_37
              let assump_44 := assump_32 assump_71
              apply False.elim assump_44
        case inr assump_29 =>
          cases assump_7
          case intro assump_50 assump_51 =>
            cases assump_51
            case intro assump_54 assump_55 =>
              have assump_72 : p3 := by
                exact assump_55
              let assump_62 := assump_50 assump_72
              apply False.elim assump_62
  let assump_4 := assump_1 assump_69
  apply False.elim assump_4


variable (p4 p1 p0 p2 p6 : Prop)
theorem file30_44846 : (((((p0 → False) ∨ (p0 ∧ p1)) ∧ ((False → p1) → False)) ∧ (((True ∨ p4) ∧ (p4 ∨ p2)) ∧ ((p1 ∨ True) → (p2 → p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              cases assump_15
              case inl assump_20 =>
                have assump_168 : (False → p1) := by
                  intro assump_30
                  apply False.elim assump_30
                let assump_29 := assump_5 assump_168
                apply False.elim assump_29
              case inr assump_21 =>
                have assump_169 : (False → p1) := by
                  intro assump_45
                  apply False.elim assump_45
                let assump_44 := assump_5 assump_169
                apply False.elim assump_44
            case inr assump_17 =>
              cases assump_15
              case inl assump_53 =>
                have assump_170 : (False → p1) := by
                  intro assump_64
                  apply False.elim assump_64
                let assump_63 := assump_5 assump_170
                apply False.elim assump_63
              case inr assump_54 =>
                have assump_171 : (False → p1) := by
                  intro assump_80
                  apply False.elim assump_80
                let assump_79 := assump_5 assump_171
                apply False.elim assump_79
      case inr assump_7 =>
        cases assump_7
        case intro assump_86 assump_87 =>
          cases assump_3
          case intro assump_94 assump_95 =>
            cases assump_94
            case intro assump_96 assump_97 =>
              cases assump_96
              case inl assump_98 =>
                cases assump_97
                case inl assump_102 =>
                  have assump_172 : (False → p1) := by
                    intro assump_112
                    apply False.elim assump_112
                  let assump_111 := assump_5 assump_172
                  apply False.elim assump_111
                case inr assump_103 =>
                  have assump_173 : (False → p1) := by
                    intro assump_127
                    apply False.elim assump_127
                  let assump_126 := assump_5 assump_173
                  apply False.elim assump_126
              case inr assump_99 =>
                cases assump_97
                case inl assump_135 =>
                  have assump_174 : (False → p1) := by
                    intro assump_146
                    apply False.elim assump_146
                  let assump_145 := assump_5 assump_174
                  apply False.elim assump_145
                case inr assump_136 =>
                  have assump_175 : (False → p1) := by
                    intro assump_162
                    apply False.elim assump_162
                  let assump_161 := assump_5 assump_175
                  apply False.elim assump_161


variable (p7 p4 p6 p1 p2 p0 p3 p5 : Prop)
theorem file30_48085 : (((((p0 ∨ p5) ∧ (p4 → False)) ∨ ((p5 ∧ False) ∨ (True → False))) ∧ (((True ∨ p3) ∧ (p6 ∨ p4)) ∧ ((True ∨ p7) ∨ (p0 → p3)))) → ((((p5 → False) → (p4 → p5)) ∧ ((p4 ∧ p3) ∨ (p2 ∧ p4))) → (((True → p0) ∨ (p3 → False)) ∧ ((p0 ∧ p3) → (p1 ∨ p6))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          cases assump_15
          case inl assump_17 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_19
              case inl assump_21 =>
                cases assump_16
                case intro assump_27 assump_28 =>
                  cases assump_27
                  case intro assump_29 assump_30 =>
                    cases assump_29
                    case inl assump_31 =>
                      cases assump_30
                      case inl assump_35 =>
                        cases assump_28
                        case inl assump_39 =>
                          cases assump_39
                          case inl assump_41 =>
                            apply Or.inl
                            intro assump_45
                            exact assump_21
                          case inr assump_42 =>
                            apply Or.inl
                            intro assump_50
                            exact assump_21
                        case inr assump_40 =>
                          apply Or.inl
                          intro assump_55
                          exact assump_21
                      case inr assump_36 =>
                        cases assump_28
                        case inl assump_60 =>
                          cases assump_60
                          case inl assump_62 =>
                            apply Or.inl
                            intro assump_66
                            exact assump_21
                          case inr assump_63 =>
                            apply Or.inl
                            intro assump_71
                            exact assump_21
                        case inr assump_61 =>
                          apply Or.inl
                          intro assump_76
                          exact assump_21
                    case inr assump_32 =>
                      cases assump_30
                      case inl assump_81 =>
                        cases assump_28
                        case inl assump_85 =>
                          cases assump_85
                          case inl assump_87 =>
                            apply Or.inl
                            intro assump_91
                            exact assump_21
                          case inr assump_88 =>
                            apply Or.inl
                            intro assump_96
                            exact assump_21
                        case inr assump_86 =>
                          apply Or.inl
                          intro assump_101
                          exact assump_21
                      case inr assump_82 =>
                        cases assump_28
                        case inl assump_106 =>
                          cases assump_106
                          case inl assump_108 =>
                            apply Or.inl
                            intro assump_112
                            exact assump_21
                          case inr assump_109 =>
                            apply Or.inl
                            intro assump_117
                            exact assump_21
                        case inr assump_107 =>
                          apply Or.inl
                          intro assump_122
                          exact assump_21
              case inr assump_22 =>
                cases assump_16
                case intro assump_129 assump_130 =>
                  cases assump_129
                  case intro assump_131 assump_132 =>
                    cases assump_131
                    case inl assump_133 =>
                      cases assump_132
                      case inl assump_137 =>
                        cases assump_130
                        case inl assump_141 =>
                          cases assump_141
                          case inl assump_143 =>
                            apply Or.inl
                            intro assump_147
                            have assump_1640 : p4 := by
                              exact assump_9
                            let assump_151 := assump_20 assump_1640
                            apply False.elim assump_151
                          case inr assump_144 =>
                            apply Or.inl
                            intro assump_157
                            have assump_1641 : p4 := by
                              exact assump_9
                            let assump_162 := assump_20 assump_1641
                            apply False.elim assump_162
                        case inr assump_142 =>
                          apply Or.inl
                          intro assump_168
                          have assump_1642 : p4 := by
                            exact assump_9
                          let assump_173 := assump_20 assump_1642
                          apply False.elim assump_173
                      case inr assump_138 =>
                        cases assump_130
                        case inl assump_179 =>
                          cases assump_179
                          case inl assump_181 =>
                            apply Or.inl
                            intro assump_185
                            have assump_1643 : p4 := by
                              exact assump_138
                            let assump_189 := assump_20 assump_1643
                            apply False.elim assump_189
                          case inr assump_182 =>
                            apply Or.inl
                            intro assump_195
                            have assump_1644 : p4 := by
                              exact assump_138
                            let assump_200 := assump_20 assump_1644
                            apply False.elim assump_200
                        case inr assump_180 =>
                          apply Or.inl
                          intro assump_206
                          have assump_1645 : p4 := by
                            exact assump_138
                          let assump_211 := assump_20 assump_1645
                          apply False.elim assump_211
                    case inr assump_134 =>
                      cases assump_132
                      case inl assump_217 =>
                        cases assump_130
                        case inl assump_221 =>
                          cases assump_221
                          case inl assump_223 =>
                            apply Or.inl
                            intro assump_227
                            have assump_1646 : p4 := by
                              exact assump_9
                            let assump_232 := assump_20 assump_1646
                            apply False.elim assump_232
                          case inr assump_224 =>
                            apply Or.inl
                            intro assump_238
                            have assump_1647 : p4 := by
                              exact assump_9
                            let assump_244 := assump_20 assump_1647
                            apply False.elim assump_244
                        case inr assump_222 =>
                          apply Or.inl
                          intro assump_250
                          have assump_1648 : p4 := by
                            exact assump_9
                          let assump_256 := assump_20 assump_1648
                          apply False.elim assump_256
                      case inr assump_218 =>
                        cases assump_130
                        case inl assump_262 =>
                          cases assump_262
                          case inl assump_264 =>
                            apply Or.inl
                            intro assump_268
                            have assump_1649 : p4 := by
                              exact assump_218
                            let assump_273 := assump_20 assump_1649
                            apply False.elim assump_273
                          case inr assump_265 =>
                            apply Or.inl
                            intro assump_279
                            have assump_1650 : p4 := by
                              exact assump_218
                            let assump_285 := assump_20 assump_1650
                            apply False.elim assump_285
                        case inr assump_263 =>
                          apply Or.inl
                          intro assump_291
                          have assump_1651 : p4 := by
                            exact assump_218
                          let assump_297 := assump_20 assump_1651
                          apply False.elim assump_297
          case inr assump_18 =>
            cases assump_18
            case inl assump_301 =>
              cases assump_301
              case intro assump_303 assump_304 =>
                apply False.elim assump_304
            case inr assump_302 =>
              cases assump_16
              case intro assump_311 assump_312 =>
                cases assump_311
                case intro assump_313 assump_314 =>
                  cases assump_313
                  case inl assump_315 =>
                    cases assump_314
                    case inl assump_319 =>
                      cases assump_312
                      case inl assump_323 =>
                        cases assump_323
                        case inl assump_325 =>
                          apply Or.inl
                          intro assump_329
                          have assump_1652 : True := by
                            apply True.intro
                          let assump_333 := assump_302 assump_1652
                          apply False.elim assump_333
                        case inr assump_326 =>
                          apply Or.inl
                          intro assump_339
                          have assump_1653 : True := by
                            apply True.intro
                          let assump_344 := assump_302 assump_1653
                          apply False.elim assump_344
                      case inr assump_324 =>
                        apply Or.inl
                        intro assump_350
                        have assump_1654 : True := by
                          apply True.intro
                        let assump_355 := assump_302 assump_1654
                        apply False.elim assump_355
                    case inr assump_320 =>
                      cases assump_312
                      case inl assump_361 =>
                        cases assump_361
                        case inl assump_363 =>
                          apply Or.inl
                          intro assump_367
                          have assump_1655 : True := by
                            apply True.intro
                          let assump_371 := assump_302 assump_1655
                          apply False.elim assump_371
                        case inr assump_364 =>
                          apply Or.inl
                          intro assump_377
                          have assump_1656 : True := by
                            apply True.intro
                          let assump_382 := assump_302 assump_1656
                          apply False.elim assump_382
                      case inr assump_362 =>
                        apply Or.inl
                        intro assump_388
                        have assump_1657 : True := by
                          apply True.intro
                        let assump_393 := assump_302 assump_1657
                        apply False.elim assump_393
                  case inr assump_316 =>
                    cases assump_314
                    case inl assump_399 =>
                      cases assump_312
                      case inl assump_403 =>
                        cases assump_403
                        case inl assump_405 =>
                          apply Or.inl
                          intro assump_409
                          have assump_1658 : True := by
                            apply True.intro
                          let assump_414 := assump_302 assump_1658
                          apply False.elim assump_414
                        case inr assump_406 =>
                          apply Or.inl
                          intro assump_420
                          have assump_1659 : True := by
                            apply True.intro
                          let assump_426 := assump_302 assump_1659
                          apply False.elim assump_426
                      case inr assump_404 =>
                        apply Or.inl
                        intro assump_432
                        have assump_1660 : True := by
                          apply True.intro
                        let assump_438 := assump_302 assump_1660
                        apply False.elim assump_438
                    case inr assump_400 =>
                      cases assump_312
                      case inl assump_444 =>
                        cases assump_444
                        case inl assump_446 =>
                          apply Or.inl
                          intro assump_450
                          have assump_1661 : True := by
                            apply True.intro
                          let assump_455 := assump_302 assump_1661
                          apply False.elim assump_455
                        case inr assump_447 =>
                          apply Or.inl
                          intro assump_461
                          have assump_1662 : True := by
                            apply True.intro
                          let assump_467 := assump_302 assump_1662
                          apply False.elim assump_467
                      case inr assump_445 =>
                        apply Or.inl
                        intro assump_473
                        have assump_1663 : True := by
                          apply True.intro
                        let assump_479 := assump_302 assump_1663
                        apply False.elim assump_479
    case inr assump_8 =>
      cases assump_8
      case intro assump_483 assump_484 =>
        cases assump_1
        case intro assump_489 assump_490 =>
          cases assump_489
          case inl assump_491 =>
            cases assump_491
            case intro assump_493 assump_494 =>
              cases assump_493
              case inl assump_495 =>
                cases assump_490
                case intro assump_501 assump_502 =>
                  cases assump_501
                  case intro assump_503 assump_504 =>
                    cases assump_503
                    case inl assump_505 =>
                      cases assump_504
                      case inl assump_509 =>
                        cases assump_502
                        case inl assump_513 =>
                          cases assump_513
                          case inl assump_515 =>
                            apply Or.inl
                            intro assump_519
                            exact assump_495
                          case inr assump_516 =>
                            apply Or.inl
                            intro assump_524
                            exact assump_495
                        case inr assump_514 =>
                          apply Or.inl
                          intro assump_529
                          exact assump_495
                      case inr assump_510 =>
                        cases assump_502
                        case inl assump_534 =>
                          cases assump_534
                          case inl assump_536 =>
                            apply Or.inl
                            intro assump_540
                            exact assump_495
                          case inr assump_537 =>
                            apply Or.inl
                            intro assump_545
                            exact assump_495
                        case inr assump_535 =>
                          apply Or.inl
                          intro assump_550
                          exact assump_495
                    case inr assump_506 =>
                      cases assump_504
                      case inl assump_555 =>
                        cases assump_502
                        case inl assump_559 =>
                          cases assump_559
                          case inl assump_561 =>
                            apply Or.inl
                            intro assump_565
                            exact assump_495
                          case inr assump_562 =>
                            apply Or.inl
                            intro assump_570
                            exact assump_495
                        case inr assump_560 =>
                          apply Or.inl
                          intro assump_575
                          exact assump_495
                      case inr assump_556 =>
                        cases assump_502
                        case inl assump_580 =>
                          cases assump_580
                          case inl assump_582 =>
                            apply Or.inl
                            intro assump_586
                            exact assump_495
                          case inr assump_583 =>
                            apply Or.inl
                            intro assump_591
                            exact assump_495
                        case inr assump_581 =>
                          apply Or.inl
                          intro assump_596
                          exact assump_495
              case inr assump_496 =>
                cases assump_490
                case intro assump_603 assump_604 =>
                  cases assump_603
                  case intro assump_605 assump_606 =>
                    cases assump_605
                    case inl assump_607 =>
                      cases assump_606
                      case inl assump_611 =>
                        cases assump_604
                        case inl assump_615 =>
                          cases assump_615
                          case inl assump_617 =>
                            apply Or.inl
                            intro assump_621
                            have assump_1664 : p4 := by
                              exact assump_484
                            let assump_625 := assump_494 assump_1664
                            apply False.elim assump_625
                          case inr assump_618 =>
                            apply Or.inl
                            intro assump_631
                            have assump_1665 : p4 := by
                              exact assump_484
                            let assump_636 := assump_494 assump_1665
                            apply False.elim assump_636
                        case inr assump_616 =>
                          apply Or.inl
                          intro assump_642
                          have assump_1666 : p4 := by
                            exact assump_484
                          let assump_647 := assump_494 assump_1666
                          apply False.elim assump_647
                      case inr assump_612 =>
                        cases assump_604
                        case inl assump_653 =>
                          cases assump_653
                          case inl assump_655 =>
                            apply Or.inl
                            intro assump_659
                            have assump_1667 : p4 := by
                              exact assump_612
                            let assump_663 := assump_494 assump_1667
                            apply False.elim assump_663
                          case inr assump_656 =>
                            apply Or.inl
                            intro assump_669
                            have assump_1668 : p4 := by
                              exact assump_612
                            let assump_674 := assump_494 assump_1668
                            apply False.elim assump_674
                        case inr assump_654 =>
                          apply Or.inl
                          intro assump_680
                          have assump_1669 : p4 := by
                            exact assump_612
                          let assump_685 := assump_494 assump_1669
                          apply False.elim assump_685
                    case inr assump_608 =>
                      cases assump_606
                      case inl assump_691 =>
                        cases assump_604
                        case inl assump_695 =>
                          cases assump_695
                          case inl assump_697 =>
                            apply Or.inl
                            intro assump_701
                            have assump_1670 : p4 := by
                              exact assump_484
                            let assump_706 := assump_494 assump_1670
                            apply False.elim assump_706
                          case inr assump_698 =>
                            apply Or.inl
                            intro assump_712
                            have assump_1671 : p4 := by
                              exact assump_484
                            let assump_718 := assump_494 assump_1671
                            apply False.elim assump_718
                        case inr assump_696 =>
                          apply Or.inl
                          intro assump_724
                          have assump_1672 : p4 := by
                            exact assump_484
                          let assump_730 := assump_494 assump_1672
                          apply False.elim assump_730
                      case inr assump_692 =>
                        cases assump_604
                        case inl assump_736 =>
                          cases assump_736
                          case inl assump_738 =>
                            apply Or.inl
                            intro assump_742
                            have assump_1673 : p4 := by
                              exact assump_692
                            let assump_747 := assump_494 assump_1673
                            apply False.elim assump_747
                          case inr assump_739 =>
                            apply Or.inl
                            intro assump_753
                            have assump_1674 : p4 := by
                              exact assump_692
                            let assump_759 := assump_494 assump_1674
                            apply False.elim assump_759
                        case inr assump_737 =>
                          apply Or.inl
                          intro assump_765
                          have assump_1675 : p4 := by
                            exact assump_692
                          let assump_771 := assump_494 assump_1675
                          apply False.elim assump_771
          case inr assump_492 =>
            cases assump_492
            case inl assump_775 =>
              cases assump_775
              case intro assump_777 assump_778 =>
                apply False.elim assump_778
            case inr assump_776 =>
              cases assump_490
              case intro assump_785 assump_786 =>
                cases assump_785
                case intro assump_787 assump_788 =>
                  cases assump_787
                  case inl assump_789 =>
                    cases assump_788
                    case inl assump_793 =>
                      cases assump_786
                      case inl assump_797 =>
                        cases assump_797
                        case inl assump_799 =>
                          apply Or.inl
                          intro assump_803
                          have assump_1676 : True := by
                            apply True.intro
                          let assump_807 := assump_776 assump_1676
                          apply False.elim assump_807
                        case inr assump_800 =>
                          apply Or.inl
                          intro assump_813
                          have assump_1677 : True := by
                            apply True.intro
                          let assump_818 := assump_776 assump_1677
                          apply False.elim assump_818
                      case inr assump_798 =>
                        apply Or.inl
                        intro assump_824
                        have assump_1678 : True := by
                          apply True.intro
                        let assump_829 := assump_776 assump_1678
                        apply False.elim assump_829
                    case inr assump_794 =>
                      cases assump_786
                      case inl assump_835 =>
                        cases assump_835
                        case inl assump_837 =>
                          apply Or.inl
                          intro assump_841
                          have assump_1679 : True := by
                            apply True.intro
                          let assump_845 := assump_776 assump_1679
                          apply False.elim assump_845
                        case inr assump_838 =>
                          apply Or.inl
                          intro assump_851
                          have assump_1680 : True := by
                            apply True.intro
                          let assump_856 := assump_776 assump_1680
                          apply False.elim assump_856
                      case inr assump_836 =>
                        apply Or.inl
                        intro assump_862
                        have assump_1681 : True := by
                          apply True.intro
                        let assump_867 := assump_776 assump_1681
                        apply False.elim assump_867
                  case inr assump_790 =>
                    cases assump_788
                    case inl assump_873 =>
                      cases assump_786
                      case inl assump_877 =>
                        cases assump_877
                        case inl assump_879 =>
                          apply Or.inl
                          intro assump_883
                          have assump_1682 : True := by
                            apply True.intro
                          let assump_888 := assump_776 assump_1682
                          apply False.elim assump_888
                        case inr assump_880 =>
                          apply Or.inl
                          intro assump_894
                          have assump_1683 : True := by
                            apply True.intro
                          let assump_900 := assump_776 assump_1683
                          apply False.elim assump_900
                      case inr assump_878 =>
                        apply Or.inl
                        intro assump_906
                        have assump_1684 : True := by
                          apply True.intro
                        let assump_912 := assump_776 assump_1684
                        apply False.elim assump_912
                    case inr assump_874 =>
                      cases assump_786
                      case inl assump_918 =>
                        cases assump_918
                        case inl assump_920 =>
                          apply Or.inl
                          intro assump_924
                          have assump_1685 : True := by
                            apply True.intro
                          let assump_929 := assump_776 assump_1685
                          apply False.elim assump_929
                        case inr assump_921 =>
                          apply Or.inl
                          intro assump_935
                          have assump_1686 : True := by
                            apply True.intro
                          let assump_941 := assump_776 assump_1686
                          apply False.elim assump_941
                      case inr assump_919 =>
                        apply Or.inl
                        intro assump_947
                        have assump_1687 : True := by
                          apply True.intro
                        let assump_953 := assump_776 assump_1687
                        apply False.elim assump_953
  intro assump_957
  cases assump_957
  case intro assump_958 assump_959 =>
    cases assump_2
    case intro assump_964 assump_965 =>
      cases assump_965
      case inl assump_968 =>
        cases assump_968
        case intro assump_970 assump_971 =>
          cases assump_1
          case intro assump_976 assump_977 =>
            cases assump_976
            case inl assump_978 =>
              cases assump_978
              case intro assump_980 assump_981 =>
                cases assump_980
                case inl assump_982 =>
                  cases assump_977
                  case intro assump_988 assump_989 =>
                    cases assump_988
                    case intro assump_990 assump_991 =>
                      cases assump_990
                      case inl assump_992 =>
                        cases assump_991
                        case inl assump_996 =>
                          cases assump_989
                          case inl assump_1000 =>
                            cases assump_1000
                            case inl assump_1002 =>
                              apply Or.inr
                              exact assump_996
                            case inr assump_1003 =>
                              apply Or.inr
                              exact assump_996
                          case inr assump_1001 =>
                            apply Or.inr
                            exact assump_996
                        case inr assump_997 =>
                          cases assump_989
                          case inl assump_1012 =>
                            cases assump_1012
                            case inl assump_1014 =>
                              have assump_1688 : p4 := by
                                exact assump_997
                              let assump_1019 := assump_981 assump_1688
                              apply False.elim assump_1019
                            case inr assump_1015 =>
                              have assump_1689 : p4 := by
                                exact assump_997
                              let assump_1027 := assump_981 assump_1689
                              apply False.elim assump_1027
                          case inr assump_1013 =>
                            have assump_1690 : p4 := by
                              exact assump_997
                            let assump_1036 := assump_981 assump_1690
                            apply False.elim assump_1036
                      case inr assump_993 =>
                        cases assump_991
                        case inl assump_1042 =>
                          cases assump_989
                          case inl assump_1046 =>
                            cases assump_1046
                            case inl assump_1048 =>
                              apply Or.inr
                              exact assump_1042
                            case inr assump_1049 =>
                              apply Or.inr
                              exact assump_1042
                          case inr assump_1047 =>
                            apply Or.inr
                            exact assump_1042
                        case inr assump_1043 =>
                          cases assump_989
                          case inl assump_1058 =>
                            cases assump_1058
                            case inl assump_1060 =>
                              have assump_1691 : p4 := by
                                exact assump_1043
                              let assump_1066 := assump_981 assump_1691
                              apply False.elim assump_1066
                            case inr assump_1061 =>
                              have assump_1692 : p4 := by
                                exact assump_1043
                              let assump_1075 := assump_981 assump_1692
                              apply False.elim assump_1075
                          case inr assump_1059 =>
                            have assump_1693 : p4 := by
                              exact assump_1043
                            let assump_1085 := assump_981 assump_1693
                            apply False.elim assump_1085
                case inr assump_983 =>
                  cases assump_977
                  case intro assump_1093 assump_1094 =>
                    cases assump_1093
                    case intro assump_1095 assump_1096 =>
                      cases assump_1095
                      case inl assump_1097 =>
                        cases assump_1096
                        case inl assump_1101 =>
                          cases assump_1094
                          case inl assump_1105 =>
                            cases assump_1105
                            case inl assump_1107 =>
                              apply Or.inr
                              exact assump_1101
                            case inr assump_1108 =>
                              apply Or.inr
                              exact assump_1101
                          case inr assump_1106 =>
                            apply Or.inr
                            exact assump_1101
                        case inr assump_1102 =>
                          cases assump_1094
                          case inl assump_1117 =>
                            cases assump_1117
                            case inl assump_1119 =>
                              have assump_1694 : p4 := by
                                exact assump_1102
                              let assump_1124 := assump_981 assump_1694
                              apply False.elim assump_1124
                            case inr assump_1120 =>
                              have assump_1695 : p4 := by
                                exact assump_1102
                              let assump_1132 := assump_981 assump_1695
                              apply False.elim assump_1132
                          case inr assump_1118 =>
                            have assump_1696 : p4 := by
                              exact assump_1102
                            let assump_1141 := assump_981 assump_1696
                            apply False.elim assump_1141
                      case inr assump_1098 =>
                        cases assump_1096
                        case inl assump_1147 =>
                          cases assump_1094
                          case inl assump_1151 =>
                            cases assump_1151
                            case inl assump_1153 =>
                              apply Or.inr
                              exact assump_1147
                            case inr assump_1154 =>
                              apply Or.inr
                              exact assump_1147
                          case inr assump_1152 =>
                            apply Or.inr
                            exact assump_1147
                        case inr assump_1148 =>
                          cases assump_1094
                          case inl assump_1163 =>
                            cases assump_1163
                            case inl assump_1165 =>
                              have assump_1697 : p4 := by
                                exact assump_1148
                              let assump_1171 := assump_981 assump_1697
                              apply False.elim assump_1171
                            case inr assump_1166 =>
                              have assump_1698 : p4 := by
                                exact assump_1148
                              let assump_1180 := assump_981 assump_1698
                              apply False.elim assump_1180
                          case inr assump_1164 =>
                            have assump_1699 : p4 := by
                              exact assump_1148
                            let assump_1190 := assump_981 assump_1699
                            apply False.elim assump_1190
            case inr assump_979 =>
              cases assump_979
              case inl assump_1194 =>
                cases assump_1194
                case intro assump_1196 assump_1197 =>
                  apply False.elim assump_1197
              case inr assump_1195 =>
                cases assump_977
                case intro assump_1204 assump_1205 =>
                  cases assump_1204
                  case intro assump_1206 assump_1207 =>
                    cases assump_1206
                    case inl assump_1208 =>
                      cases assump_1207
                      case inl assump_1212 =>
                        cases assump_1205
                        case inl assump_1216 =>
                          cases assump_1216
                          case inl assump_1218 =>
                            apply Or.inr
                            exact assump_1212
                          case inr assump_1219 =>
                            apply Or.inr
                            exact assump_1212
                        case inr assump_1217 =>
                          apply Or.inr
                          exact assump_1212
                      case inr assump_1213 =>
                        cases assump_1205
                        case inl assump_1228 =>
                          cases assump_1228
                          case inl assump_1230 =>
                            have assump_1700 : True := by
                              apply True.intro
                            let assump_1235 := assump_1195 assump_1700
                            apply False.elim assump_1235
                          case inr assump_1231 =>
                            have assump_1701 : True := by
                              apply True.intro
                            let assump_1243 := assump_1195 assump_1701
                            apply False.elim assump_1243
                        case inr assump_1229 =>
                          have assump_1702 : True := by
                            apply True.intro
                          let assump_1252 := assump_1195 assump_1702
                          apply False.elim assump_1252
                    case inr assump_1209 =>
                      cases assump_1207
                      case inl assump_1258 =>
                        cases assump_1205
                        case inl assump_1262 =>
                          cases assump_1262
                          case inl assump_1264 =>
                            apply Or.inr
                            exact assump_1258
                          case inr assump_1265 =>
                            apply Or.inr
                            exact assump_1258
                        case inr assump_1263 =>
                          apply Or.inr
                          exact assump_1258
                      case inr assump_1259 =>
                        cases assump_1205
                        case inl assump_1274 =>
                          cases assump_1274
                          case inl assump_1276 =>
                            have assump_1703 : True := by
                              apply True.intro
                            let assump_1282 := assump_1195 assump_1703
                            apply False.elim assump_1282
                          case inr assump_1277 =>
                            have assump_1704 : True := by
                              apply True.intro
                            let assump_1291 := assump_1195 assump_1704
                            apply False.elim assump_1291
                        case inr assump_1275 =>
                          have assump_1705 : True := by
                            apply True.intro
                          let assump_1301 := assump_1195 assump_1705
                          apply False.elim assump_1301
      case inr assump_969 =>
        cases assump_969
        case intro assump_1305 assump_1306 =>
          cases assump_1
          case intro assump_1311 assump_1312 =>
            cases assump_1311
            case inl assump_1313 =>
              cases assump_1313
              case intro assump_1315 assump_1316 =>
                cases assump_1315
                case inl assump_1317 =>
                  cases assump_1312
                  case intro assump_1323 assump_1324 =>
                    cases assump_1323
                    case intro assump_1325 assump_1326 =>
                      cases assump_1325
                      case inl assump_1327 =>
                        cases assump_1326
                        case inl assump_1331 =>
                          cases assump_1324
                          case inl assump_1335 =>
                            cases assump_1335
                            case inl assump_1337 =>
                              apply Or.inr
                              exact assump_1331
                            case inr assump_1338 =>
                              apply Or.inr
                              exact assump_1331
                          case inr assump_1336 =>
                            apply Or.inr
                            exact assump_1331
                        case inr assump_1332 =>
                          cases assump_1324
                          case inl assump_1347 =>
                            cases assump_1347
                            case inl assump_1349 =>
                              have assump_1706 : p4 := by
                                exact assump_1332
                              let assump_1354 := assump_1316 assump_1706
                              apply False.elim assump_1354
                            case inr assump_1350 =>
                              have assump_1707 : p4 := by
                                exact assump_1332
                              let assump_1362 := assump_1316 assump_1707
                              apply False.elim assump_1362
                          case inr assump_1348 =>
                            have assump_1708 : p4 := by
                              exact assump_1332
                            let assump_1371 := assump_1316 assump_1708
                            apply False.elim assump_1371
                      case inr assump_1328 =>
                        cases assump_1326
                        case inl assump_1377 =>
                          cases assump_1324
                          case inl assump_1381 =>
                            cases assump_1381
                            case inl assump_1383 =>
                              apply Or.inr
                              exact assump_1377
                            case inr assump_1384 =>
                              apply Or.inr
                              exact assump_1377
                          case inr assump_1382 =>
                            apply Or.inr
                            exact assump_1377
                        case inr assump_1378 =>
                          cases assump_1324
                          case inl assump_1393 =>
                            cases assump_1393
                            case inl assump_1395 =>
                              have assump_1709 : p4 := by
                                exact assump_1378
                              let assump_1401 := assump_1316 assump_1709
                              apply False.elim assump_1401
                            case inr assump_1396 =>
                              have assump_1710 : p4 := by
                                exact assump_1378
                              let assump_1410 := assump_1316 assump_1710
                              apply False.elim assump_1410
                          case inr assump_1394 =>
                            have assump_1711 : p4 := by
                              exact assump_1378
                            let assump_1420 := assump_1316 assump_1711
                            apply False.elim assump_1420
                case inr assump_1318 =>
                  cases assump_1312
                  case intro assump_1428 assump_1429 =>
                    cases assump_1428
                    case intro assump_1430 assump_1431 =>
                      cases assump_1430
                      case inl assump_1432 =>
                        cases assump_1431
                        case inl assump_1436 =>
                          cases assump_1429
                          case inl assump_1440 =>
                            cases assump_1440
                            case inl assump_1442 =>
                              apply Or.inr
                              exact assump_1436
                            case inr assump_1443 =>
                              apply Or.inr
                              exact assump_1436
                          case inr assump_1441 =>
                            apply Or.inr
                            exact assump_1436
                        case inr assump_1437 =>
                          cases assump_1429
                          case inl assump_1452 =>
                            cases assump_1452
                            case inl assump_1454 =>
                              have assump_1712 : p4 := by
                                exact assump_1437
                              let assump_1459 := assump_1316 assump_1712
                              apply False.elim assump_1459
                            case inr assump_1455 =>
                              have assump_1713 : p4 := by
                                exact assump_1437
                              let assump_1467 := assump_1316 assump_1713
                              apply False.elim assump_1467
                          case inr assump_1453 =>
                            have assump_1714 : p4 := by
                              exact assump_1437
                            let assump_1476 := assump_1316 assump_1714
                            apply False.elim assump_1476
                      case inr assump_1433 =>
                        cases assump_1431
                        case inl assump_1482 =>
                          cases assump_1429
                          case inl assump_1486 =>
                            cases assump_1486
                            case inl assump_1488 =>
                              apply Or.inr
                              exact assump_1482
                            case inr assump_1489 =>
                              apply Or.inr
                              exact assump_1482
                          case inr assump_1487 =>
                            apply Or.inr
                            exact assump_1482
                        case inr assump_1483 =>
                          cases assump_1429
                          case inl assump_1498 =>
                            cases assump_1498
                            case inl assump_1500 =>
                              have assump_1715 : p4 := by
                                exact assump_1483
                              let assump_1506 := assump_1316 assump_1715
                              apply False.elim assump_1506
                            case inr assump_1501 =>
                              have assump_1716 : p4 := by
                                exact assump_1483
                              let assump_1515 := assump_1316 assump_1716
                              apply False.elim assump_1515
                          case inr assump_1499 =>
                            have assump_1717 : p4 := by
                              exact assump_1483
                            let assump_1525 := assump_1316 assump_1717
                            apply False.elim assump_1525
            case inr assump_1314 =>
              cases assump_1314
              case inl assump_1529 =>
                cases assump_1529
                case intro assump_1531 assump_1532 =>
                  apply False.elim assump_1532
              case inr assump_1530 =>
                cases assump_1312
                case intro assump_1539 assump_1540 =>
                  cases assump_1539
                  case intro assump_1541 assump_1542 =>
                    cases assump_1541
                    case inl assump_1543 =>
                      cases assump_1542
                      case inl assump_1547 =>
                        cases assump_1540
                        case inl assump_1551 =>
                          cases assump_1551
                          case inl assump_1553 =>
                            apply Or.inr
                            exact assump_1547
                          case inr assump_1554 =>
                            apply Or.inr
                            exact assump_1547
                        case inr assump_1552 =>
                          apply Or.inr
                          exact assump_1547
                      case inr assump_1548 =>
                        cases assump_1540
                        case inl assump_1563 =>
                          cases assump_1563
                          case inl assump_1565 =>
                            have assump_1718 : True := by
                              apply True.intro
                            let assump_1570 := assump_1530 assump_1718
                            apply False.elim assump_1570
                          case inr assump_1566 =>
                            have assump_1719 : True := by
                              apply True.intro
                            let assump_1578 := assump_1530 assump_1719
                            apply False.elim assump_1578
                        case inr assump_1564 =>
                          have assump_1720 : True := by
                            apply True.intro
                          let assump_1587 := assump_1530 assump_1720
                          apply False.elim assump_1587
                    case inr assump_1544 =>
                      cases assump_1542
                      case inl assump_1593 =>
                        cases assump_1540
                        case inl assump_1597 =>
                          cases assump_1597
                          case inl assump_1599 =>
                            apply Or.inr
                            exact assump_1593
                          case inr assump_1600 =>
                            apply Or.inr
                            exact assump_1593
                        case inr assump_1598 =>
                          apply Or.inr
                          exact assump_1593
                      case inr assump_1594 =>
                        cases assump_1540
                        case inl assump_1609 =>
                          cases assump_1609
                          case inl assump_1611 =>
                            have assump_1721 : True := by
                              apply True.intro
                            let assump_1617 := assump_1530 assump_1721
                            apply False.elim assump_1617
                          case inr assump_1612 =>
                            have assump_1722 : True := by
                              apply True.intro
                            let assump_1626 := assump_1530 assump_1722
                            apply False.elim assump_1626
                        case inr assump_1610 =>
                          have assump_1723 : True := by
                            apply True.intro
                          let assump_1636 := assump_1530 assump_1723
                          apply False.elim assump_1636


variable (p5 p6 p1 p0 p3 p7 : Prop)
theorem file30_100934 : (((((p5 → False) ∧ (False ∧ p7)) → ((p3 ∧ p7) → False)) → (((p1 ∨ True) ∧ (False → p3)) → False)) → ((((p1 → p1) ∨ (p6 → False)) ∨ ((True → False) → (p6 → p3))) → (((p1 → p0) ∨ (p3 → True)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      cases assump_8
      case inl assump_10 =>
        have assump_186 : (((p5 → False) ∧ (False ∧ p7)) → ((p3 ∧ p7) → False)) := by
          intro assump_17
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            cases assump_17
            case intro assump_25 assump_26 =>
              cases assump_26
              case intro assump_29 assump_30 =>
                apply False.elim assump_29
        let assump_16 := assump_1 assump_186
        have assump_187 : ((p1 ∨ True) ∧ (False → p3)) := by
          apply And.intro
          apply Or.inr
          apply True.intro
          intro assump_34
          apply False.elim assump_34
        let assump_33 := assump_16 assump_187
        apply False.elim assump_33
      case inr assump_11 =>
        have assump_188 : (((p5 → False) ∧ (False ∧ p7)) → ((p3 ∧ p7) → False)) := by
          intro assump_45
          intro assump_46
          cases assump_46
          case intro assump_47 assump_48 =>
            cases assump_45
            case intro assump_53 assump_54 =>
              cases assump_54
              case intro assump_57 assump_58 =>
                apply False.elim assump_57
        let assump_44 := assump_1 assump_188
        have assump_189 : ((p1 ∨ True) ∧ (False → p3)) := by
          apply And.intro
          apply Or.inr
          apply True.intro
          intro assump_62
          apply False.elim assump_62
        let assump_61 := assump_44 assump_189
        apply False.elim assump_61
    case inr assump_9 =>
      have assump_190 : (((p5 → False) ∧ (False ∧ p7)) → ((p3 ∧ p7) → False)) := by
        intro assump_73
        intro assump_74
        cases assump_74
        case intro assump_75 assump_76 =>
          cases assump_73
          case intro assump_81 assump_82 =>
            cases assump_82
            case intro assump_85 assump_86 =>
              apply False.elim assump_85
      let assump_72 := assump_1 assump_190
      have assump_191 : ((p1 ∨ True) ∧ (False → p3)) := by
        apply And.intro
        apply Or.inr
        apply True.intro
        intro assump_90
        apply False.elim assump_90
      let assump_89 := assump_72 assump_191
      apply False.elim assump_89
  case inr assump_5 =>
    cases assump_2
    case inl assump_98 =>
      cases assump_98
      case inl assump_100 =>
        have assump_192 : (((p5 → False) ∧ (False ∧ p7)) → ((p3 ∧ p7) → False)) := by
          intro assump_107
          intro assump_108
          cases assump_108
          case intro assump_109 assump_110 =>
            cases assump_107
            case intro assump_115 assump_116 =>
              cases assump_116
              case intro assump_119 assump_120 =>
                apply False.elim assump_119
        let assump_106 := assump_1 assump_192
        have assump_193 : ((p1 ∨ True) ∧ (False → p3)) := by
          apply And.intro
          apply Or.inr
          apply True.intro
          intro assump_124
          apply False.elim assump_124
        let assump_123 := assump_106 assump_193
        apply False.elim assump_123
      case inr assump_101 =>
        have assump_194 : (((p5 → False) ∧ (False ∧ p7)) → ((p3 ∧ p7) → False)) := by
          intro assump_135
          intro assump_136
          cases assump_136
          case intro assump_137 assump_138 =>
            cases assump_135
            case intro assump_143 assump_144 =>
              cases assump_144
              case intro assump_147 assump_148 =>
                apply False.elim assump_147
        let assump_134 := assump_1 assump_194
        have assump_195 : ((p1 ∨ True) ∧ (False → p3)) := by
          apply And.intro
          apply Or.inr
          apply True.intro
          intro assump_152
          apply False.elim assump_152
        let assump_151 := assump_134 assump_195
        apply False.elim assump_151
    case inr assump_99 =>
      have assump_196 : (((p5 → False) ∧ (False ∧ p7)) → ((p3 ∧ p7) → False)) := by
        intro assump_163
        intro assump_164
        cases assump_164
        case intro assump_165 assump_166 =>
          cases assump_163
          case intro assump_171 assump_172 =>
            cases assump_172
            case intro assump_175 assump_176 =>
              apply False.elim assump_175
      let assump_162 := assump_1 assump_196
      have assump_197 : ((p1 ∨ True) ∧ (False → p3)) := by
        apply And.intro
        apply Or.inr
        apply True.intro
        intro assump_180
        apply False.elim assump_180
      let assump_179 := assump_162 assump_197
      apply False.elim assump_179


variable (p5 p0 p1 p2 : Prop)
theorem file30_105958 : ((((((True → False) → (p0 ∨ True)) ∧ ((False → False) → False)) → (((p2 ∧ p5) → (p0 → False)) ∨ ((p1 ∧ True) ∨ (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_35 : ((((True → False) → (p0 ∨ True)) ∧ ((False → False) → False)) → (((p2 ∧ p5) → (p0 → False)) ∨ ((p1 ∧ True) ∨ (p0 → False)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      intro assump_13
      cases assump_12
      case intro assump_16 assump_17 =>
        have assump_36 : (False → False) := by
          intro assump_26
          apply False.elim assump_26
        let assump_25 := assump_7 assump_36
        apply False.elim assump_25
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p0 p6 p7 p4 p5 p3 p2 : Prop)
theorem file30_106792 : (((((p0 → False) → (p7 → p6)) → False) → (((p0 ∨ p0) ∧ (p7 → p7)) → False)) ∨ ((((p3 → p7) ∧ (p5 ∨ p0)) → False) ∧ (((p2 → False) → False) ∨ ((p4 ∨ p4) ∨ (p5 → p7))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      have assump_47 : ((p0 → False) → (p7 → p6)) := by
        intro assump_14
        intro assump_15
        have assump_48 : p0 := by
          exact assump_5
        let assump_20 := assump_14 assump_48
        apply False.elim assump_20
      let assump_13 := assump_1 assump_47
      apply False.elim assump_13
    case inr assump_6 =>
      have assump_49 : ((p0 → False) → (p7 → p6)) := by
        intro assump_34
        intro assump_35
        have assump_50 : p0 := by
          exact assump_6
        let assump_40 := assump_34 assump_50
        apply False.elim assump_40
      let assump_33 := assump_1 assump_49
      apply False.elim assump_33


variable (p6 p7 p5 p3 p4 p0 : Prop)
theorem file30_107831 : (((((True ∧ False) ∧ (p4 ∨ p0)) ∧ ((p3 → False) → False)) → False) ∨ ((((p3 → False) ∧ (p7 ∨ p6)) ∨ ((p5 ∧ p5) ∧ (p4 ∧ False))) → False)) := by
  apply Or.inl
  intro assump_23
  cases assump_23
  case intro assump_24 assump_25 =>
    cases assump_24
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        apply False.elim assump_29


variable (p3 p7 p1 p4 p2 p0 : Prop)
theorem file30_108277 : ((((((p1 ∧ p0) ∨ (p2 ∨ p0)) ∧ ((True → False) ∨ (p0 ∧ p0))) → (((p0 → False) → (p0 ∧ p7)) ∨ ((p0 → False) → (p1 ∨ False)))) ∧ ((((p3 → p1) → (p4 → False)) → False) ∧ (((p0 ∧ p1) ∧ (p2 ∨ p4)) ∧ ((False → False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case inl assump_20 =>
              have assump_44 : (False → False) := by
                intro assump_27
                apply False.elim assump_27
              let assump_26 := assump_11 assump_44
              apply False.elim assump_26
            case inr assump_21 =>
              have assump_45 : (False → False) := by
                intro assump_38
                apply False.elim assump_38
              let assump_37 := assump_11 assump_45
              apply False.elim assump_37


variable (p2 p1 p0 p4 p6 p7 p5 p3 : Prop)
theorem file30_109436 : ((((((True ∨ p1) → False) → ((p7 → p4) → (p4 ∨ p3))) → False) ∧ ((((p5 ∧ p0) ∨ (p2 ∨ p7)) ∨ ((p3 → p0) → (p6 ∨ True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p5 ∧ p0) ∨ (p2 ∨ p7)) ∨ ((p3 → p0) → (p6 ∨ True))) := by
      apply Or.inr
      intro assump_9
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p1 p6 p4 p7 p3 p0 p5 : Prop)
theorem file30_109943 : (((((p7 → p4) → False) → False) → (((p5 → False) ∧ (False ∧ p0)) → False)) ∨ ((((False → False) ∧ (p7 ∨ p3)) ∨ ((p3 → False) → False)) ∧ (((True ∨ p4) ∧ (p3 ∨ p1)) ∨ ((p6 ∨ p4) ∧ (p6 ∧ p4))))) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_8
    case intro assump_11 assump_12 =>
      apply False.elim assump_11


variable (p6 p2 p7 : Prop)
theorem file30_110383 : ((((((p2 → False) ∧ (p7 ∧ p6)) ∧ ((True ∨ p2) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_27 : ((((p2 → False) ∧ (p7 ∧ p6)) ∧ ((True ∨ p2) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          have assump_28 : (True ∨ p2) := by
            apply Or.inl
            apply True.intro
          let assump_20 := assump_7 assump_28
          apply False.elim assump_20
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p7 p1 p0 p2 p3 p5 : Prop)
theorem file30_111082 : ((((((p3 ∨ p0) → (True ∨ p2)) → False) → (((p5 → p3) → False) ∧ ((p1 → p2) → (p7 → p2)))) → False) → False) := by
  intro assump_67
  have assump_110 : ((((p3 ∨ p0) → (True ∨ p2)) → False) → (((p5 → p3) → False) ∧ ((p1 → p2) → (p7 → p2)))) := by
    intro assump_71
    apply And.intro
    intro assump_72
    have assump_111 : ((p3 ∨ p0) → (True ∨ p2)) := by
      intro assump_78
      cases assump_78
      case inl assump_79 =>
        apply Or.inl
        apply True.intro
      case inr assump_80 =>
        apply Or.inl
        apply True.intro
    let assump_77 := assump_71 assump_111
    apply False.elim assump_77
    intro assump_88
    intro assump_89
    have assump_112 : ((p3 ∨ p0) → (True ∨ p2)) := by
      intro assump_97
      cases assump_97
      case inl assump_98 =>
        apply Or.inl
        apply True.intro
      case inr assump_99 =>
        apply Or.inl
        apply True.intro
    let assump_96 := assump_71 assump_112
    apply False.elim assump_96
  let assump_70 := assump_67 assump_110
  apply False.elim assump_70


variable (p5 p3 p7 p0 p1 p2 p4 : Prop)
theorem file30_112198 : (((((True ∨ p0) → False) ∧ ((p5 → False) ∨ (p5 → False))) ∧ (((False ∨ p5) ∨ (p7 ∧ p3)) → ((p1 → False) ∧ (p4 ∧ p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_30 : (True ∨ p0) := by
          apply Or.inl
          apply True.intro
        let assump_16 := assump_4 assump_30
        apply False.elim assump_16
      case inr assump_9 =>
        have assump_31 : (True ∨ p0) := by
          apply Or.inl
          apply True.intro
        let assump_26 := assump_4 assump_31
        apply False.elim assump_26


variable (p7 p2 p1 p6 p5 p3 p0 : Prop)
theorem file30_112937 : ((((((p7 ∧ p7) → (p6 → p5)) → ((p7 → False) → (p7 → False))) ∨ (((p5 ∨ p1) → False) ∨ ((True ∨ p3) ∨ (p5 → p3)))) → ((((p0 ∨ p3) ∧ (p3 ∨ p2)) ∨ ((False → False) ∧ (p3 → False))) → False)) → False) := by
  intro assump_1
  have assump_51 : ((((p7 ∧ p7) → (p6 → p5)) → ((p7 → False) → (p7 → False))) ∨ (((p5 ∨ p1) → False) ∨ ((True ∨ p3) ∨ (p5 → p3)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_52 : p7 := by
      exact assump_7
    let assump_16 := assump_6 assump_52
    apply False.elim assump_16
  let assump_4 := assump_1 assump_51
  have assump_53 : (((p0 ∨ p3) ∧ (p3 ∨ p2)) ∨ ((False → False) ∧ (p3 → False))) := by
    apply Or.inr
    apply And.intro
    intro assump_21
    apply False.elim assump_21
    intro assump_24
    have assump_54 : ((((p7 ∧ p7) → (p6 → p5)) → ((p7 → False) → (p7 → False))) ∨ (((p5 ∨ p1) → False) ∨ ((True ∨ p3) ∨ (p5 → p3)))) := by
      apply Or.inl
      intro assump_29
      intro assump_30
      intro assump_31
      have assump_55 : p7 := by
        exact assump_31
      let assump_40 := assump_30 assump_55
      apply False.elim assump_40
    let assump_28 := assump_1 assump_54
    have assump_56 : (((p0 ∨ p3) ∧ (p3 ∨ p2)) ∨ ((False → False) ∧ (p3 → False))) := by
      apply Or.inl
      apply And.intro
      apply Or.inr
      exact assump_24
      apply Or.inl
      exact assump_24
    let assump_44 := assump_28 assump_56
    apply False.elim assump_44
  let assump_20 := assump_4 assump_53
  apply False.elim assump_20


variable (p3 p7 p5 : Prop)
theorem file30_114518 : ((((((p3 → p3) ∧ (p5 → p3)) ∧ ((p7 → p7) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p3 → p3) ∧ (p5 → p3)) ∧ ((p7 → p7) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_27 : (p7 → p7) := by
          intro assump_17
          exact assump_17
        let assump_16 := assump_7 assump_27
        apply False.elim assump_16
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p4 p3 p6 p0 p7 : Prop)
theorem file30_115129 : (((((p0 → False) → False) → False) ∧ (((p3 → False) → False) → False)) → ((((p7 ∧ True) ∧ (p6 → p4)) → ((p0 ∨ p6) ∨ (p7 → True))) ∧ (((True → False) → False) ∨ ((p6 → False) ∨ (p3 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        apply Or.inr
        intro assump_19
        apply True.intro
  cases assump_1
  case intro assump_20 assump_21 =>
    apply Or.inl
    intro assump_26
    have assump_33 : True := by
      apply True.intro
    let assump_29 := assump_26 assump_33
    apply False.elim assump_29


variable (p1 p0 p5 p7 p6 : Prop)
theorem file30_115891 : (((((p1 ∨ p1) ∨ (p1 ∧ False)) ∨ ((p7 ∨ p1) ∨ (True ∨ True))) → False) → ((((p0 → p6) → False) → ((p5 → False) ∨ (True ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_11 : (((p1 ∨ p1) ∨ (p1 ∧ False)) ∨ ((p7 ∨ p1) ∨ (True ∨ True))) := by
    apply Or.inr
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p0 p6 p5 p4 p1 p3 : Prop)
theorem file30_116351 : (((((p1 → False) → (p0 → False)) → False) ∨ (((p4 ∧ True) → False) → False)) → ((((p4 → False) ∧ (False ∧ p6)) → False) ∨ (((True ∧ p3) ∨ (p4 ∧ p5)) → ((p0 ∨ p1) → False)))) := by
  intro assump_13
  cases assump_13
  case inl assump_14 =>
    apply Or.inl
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        apply False.elim assump_23
  case inr assump_15 =>
    apply Or.inl
    intro assump_29
    cases assump_29
    case intro assump_30 assump_31 =>
      cases assump_31
      case intro assump_34 assump_35 =>
        apply False.elim assump_34


variable (p1 p5 p0 p4 p7 p2 p3 p6 : Prop)
theorem file30_117065 : (((((p7 ∨ p6) → (p5 ∧ False)) ∨ ((p4 ∧ p3) ∧ (p0 ∨ p6))) → (((p0 ∨ p1) ∨ (False → False)) ∨ ((p5 ∨ p0) ∧ (p4 → False)))) ∨ ((((p5 ∨ p7) ∧ (p5 ∨ p2)) ∧ ((p7 ∧ p4) ∧ (p2 → True))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inr
    intro assump_6
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case inl assump_17 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          exact assump_17
        case inr assump_18 =>
          apply Or.inl
          apply Or.inr
          intro assump_23
          apply False.elim assump_23


variable (p2 p5 p1 p6 p4 p7 p3 p0 : Prop)
theorem file30_117908 : (((((p1 ∧ p1) ∧ (p1 → False)) → False) ∨ (((p0 ∨ False) → (p4 → False)) → ((p3 ∨ p3) ∧ (p7 → True)))) ∨ ((((p6 ∨ p7) ∨ (False ∧ p2)) ∧ ((p5 → p1) ∧ (p7 ∧ p2))) ∨ (((p4 ∨ True) ∨ (p4 → p7)) ∧ ((p7 → True) → (p1 ∨ p5))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_16 : p1 := by
        exact assump_5
      let assump_12 := assump_3 assump_16
      apply False.elim assump_12


variable (p2 p5 p3 p7 p6 p0 p1 : Prop)
theorem file30_118480 : (((((p6 ∧ p1) ∧ (p6 → p5)) ∨ ((p2 ∧ p6) → (p6 ∧ p7))) → (((True → False) → (p6 ∨ p0)) → ((True ∨ p5) ∨ (False ∧ p6)))) ∨ ((((p1 → p3) → (p1 → False)) ∨ ((True → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
  case inr assump_6 =>
    apply Or.inl
    apply Or.inl
    apply True.intro


variable (p4 p3 p5 p7 p2 p6 p1 p0 : Prop)
theorem file30_119089 : (((((False ∨ p0) → (True → p6)) ∨ ((p1 ∨ p1) → (p7 ∧ False))) → (((False → False) ∧ (p7 ∨ p3)) → ((True ∨ p2) ∨ (p0 → p5)))) ∨ ((((p6 ∧ p2) → (p2 ∧ False)) → False) ∨ (((p7 ∨ p4) → (p1 → False)) → False))) := by
  apply Or.inl
  intro assump_25
  intro assump_26
  cases assump_26
  case intro assump_27 assump_28 =>
    cases assump_28
    case inl assump_31 =>
      cases assump_25
      case inl assump_35 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_36 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
    case inr assump_32 =>
      cases assump_25
      case inl assump_43 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
      case inr assump_44 =>
        apply Or.inl
        apply Or.inl
        apply True.intro


variable (p5 p4 p6 p2 : Prop)
theorem file30_119956 : ((((((p6 ∨ p6) ∧ (p4 ∧ False)) ∧ ((p5 → False) ∨ (p6 ∨ p2))) → False) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p6 ∨ p6) ∧ (p4 ∧ False)) ∧ ((p5 → False) ∨ (p6 ∨ p2))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            apply False.elim assump_15
        case inr assump_11 =>
          cases assump_9
          case intro assump_22 assump_23 =>
            apply False.elim assump_23
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p0 p4 p5 p6 p3 p1 p7 : Prop)
theorem file30_120720 : (((((p6 → False) ∨ (p3 → False)) ∨ ((p3 → False) → False)) → (((p1 ∧ p0) → False) → ((p4 ∨ p4) ∨ (p1 → p1)))) ∨ ((((False ∧ p7) → (p4 → p1)) ∧ ((p5 ∨ p0) → (False ∨ p4))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inr
      intro assump_11
      exact assump_11
    case inr assump_8 =>
      apply Or.inr
      intro assump_16
      exact assump_16
  case inr assump_6 =>
    apply Or.inr
    intro assump_21
    exact assump_21


variable (p0 p4 p5 : Prop)
theorem file30_121322 : ((((((False → False) ∨ (True ∧ p4)) → False) → False) → ((((p4 ∨ False) → False) → ((p5 ∨ p0) ∨ (p4 → False))) → False)) → False) := by
  intro assump_33
  have assump_62 : ((((False → False) ∨ (True ∧ p4)) → False) → False) := by
    intro assump_37
    have assump_63 : ((False → False) ∨ (True ∧ p4)) := by
      apply Or.inl
      intro assump_41
      apply False.elim assump_41
    let assump_40 := assump_37 assump_63
    apply False.elim assump_40
  let assump_36 := assump_33 assump_62
  have assump_64 : (((p4 ∨ False) → False) → ((p5 ∨ p0) ∨ (p4 → False))) := by
    intro assump_48
    apply Or.inr
    intro assump_51
    have assump_65 : (p4 ∨ False) := by
      apply Or.inl
      exact assump_51
    let assump_55 := assump_48 assump_65
    apply False.elim assump_55
  let assump_47 := assump_36 assump_64
  apply False.elim assump_47


variable (p1 p6 p4 p2 p5 p3 : Prop)
theorem file30_122234 : ((((((p5 → False) → (p5 ∨ p1)) → False) → False) ∧ ((((p6 → p6) → (p2 ∧ p5)) ∨ ((p4 ∧ p4) → False)) ∧ (((p3 ∨ p1) → False) ∧ ((p1 ∨ True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          have assump_34 : (p1 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_18 := assump_13 assump_34
          apply False.elim assump_18
      case inr assump_9 =>
        cases assump_7
        case intro assump_24 assump_25 =>
          have assump_35 : (p1 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_30 := assump_25 assump_35
          apply False.elim assump_30


variable (p5 p0 p4 p1 p2 p7 p6 : Prop)
theorem file30_123156 : ((((((p7 ∨ False) ∧ (p6 ∧ p2)) ∧ ((p2 ∧ False) ∧ (p6 → False))) ∧ (((p2 ∧ p4) ∨ (p0 → False)) ∧ ((p6 → p5) → (p1 ∨ True)))) ∧ ((((p7 → False) → (p0 → p7)) ∧ ((p4 → False) → (p6 ∨ p2))) ∨ (((p2 ∧ p4) ∨ (p4 → p1)) → False))) → False) := by
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
              cases assump_7
              case intro assump_20 assump_21 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  apply False.elim assump_23
          case inr assump_11 =>
            apply False.elim assump_11


variable (p2 p7 p4 p5 p0 p6 p3 : Prop)
theorem file30_124107 : ((((((p4 → p5) → False) ∧ ((p3 → True) ∧ (p4 ∨ p0))) → (((p3 → p6) → (p0 ∨ True)) ∨ ((p0 → p5) ∨ (p2 → p4)))) ∧ ((((p6 → False) ∨ (True → False)) ∧ ((p7 ∨ True) → False)) ∧ (((p2 → False) ∨ (p3 ∧ True)) ∧ ((p6 → False) ∨ (p5 ∨ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_17
              case inl assump_22 =>
                have assump_154 : (p7 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_28 := assump_9 assump_154
                apply False.elim assump_28
              case inr assump_23 =>
                cases assump_23
                case inl assump_32 =>
                  have assump_155 : (p7 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_38 := assump_9 assump_155
                  apply False.elim assump_38
                case inr assump_33 =>
                  have assump_156 : p2 := by
                    exact assump_33
                  let assump_45 := assump_18 assump_156
                  apply False.elim assump_45
            case inr assump_19 =>
              cases assump_19
              case intro assump_49 assump_50 =>
                cases assump_17
                case inl assump_55 =>
                  have assump_157 : (p7 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_61 := assump_9 assump_157
                  apply False.elim assump_61
                case inr assump_56 =>
                  cases assump_56
                  case inl assump_65 =>
                    have assump_158 : (p7 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_71 := assump_9 assump_158
                    apply False.elim assump_71
                  case inr assump_66 =>
                    have assump_159 : (p7 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_79 := assump_9 assump_159
                    apply False.elim assump_79
        case inr assump_11 =>
          cases assump_7
          case intro assump_87 assump_88 =>
            cases assump_87
            case inl assump_89 =>
              cases assump_88
              case inl assump_93 =>
                have assump_160 : (p7 ∨ True) := by
                  apply Or.inr
                  apply True.intro
                let assump_99 := assump_9 assump_160
                apply False.elim assump_99
              case inr assump_94 =>
                cases assump_94
                case inl assump_103 =>
                  have assump_161 : (p7 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_109 := assump_9 assump_161
                  apply False.elim assump_109
                case inr assump_104 =>
                  have assump_162 : p2 := by
                    exact assump_104
                  let assump_116 := assump_89 assump_162
                  apply False.elim assump_116
            case inr assump_90 =>
              cases assump_90
              case intro assump_120 assump_121 =>
                cases assump_88
                case inl assump_126 =>
                  have assump_163 : (p7 ∨ True) := by
                    apply Or.inr
                    apply True.intro
                  let assump_132 := assump_9 assump_163
                  apply False.elim assump_132
                case inr assump_127 =>
                  cases assump_127
                  case inl assump_136 =>
                    have assump_164 : (p7 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_142 := assump_9 assump_164
                    apply False.elim assump_142
                  case inr assump_137 =>
                    have assump_165 : (p7 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_150 := assump_9 assump_165
                    apply False.elim assump_150


variable (p4 p6 p0 p3 p2 : Prop)
theorem file30_128673 : (((((p4 → p4) → False) → ((True → p0) → False)) ∧ (((p6 ∧ False) ∧ (p2 ∧ True)) ∧ ((p2 ∨ False) → (p2 → False)))) → ((((p6 ∨ p2) ∧ (p3 → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_14


variable (p3 p5 p1 p6 p0 p4 : Prop)
theorem file30_129208 : (((((False → False) → (p6 → p6)) → False) ∧ (((p5 ∧ p4) ∧ (True → False)) ∨ ((p0 ∧ p1) ∧ (p3 → False)))) → ((((p5 ∧ p0) → (p5 ∧ p6)) → ((True → True) → (p1 → p4))) → (((p6 → False) ∨ (p0 ∧ True)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_11
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            have assump_104 : True := by
              apply True.intro
            let assump_26 := assump_17 assump_104
            apply False.elim assump_26
      case inr assump_15 =>
        cases assump_15
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            have assump_105 : ((False → False) → (p6 → p6)) := by
              intro assump_44
              intro assump_45
              exact assump_45
            let assump_43 := assump_10 assump_105
            apply False.elim assump_43
  case inr assump_5 =>
    cases assump_5
    case intro assump_53 assump_54 =>
      cases assump_1
      case intro assump_61 assump_62 =>
        cases assump_62
        case inl assump_65 =>
          cases assump_65
          case intro assump_67 assump_68 =>
            cases assump_67
            case intro assump_69 assump_70 =>
              have assump_106 : True := by
                apply True.intro
              let assump_77 := assump_68 assump_106
              apply False.elim assump_77
        case inr assump_66 =>
          cases assump_66
          case intro assump_81 assump_82 =>
            cases assump_81
            case intro assump_83 assump_84 =>
              have assump_107 : ((False → False) → (p6 → p6)) := by
                intro assump_95
                intro assump_96
                exact assump_96
              let assump_94 := assump_61 assump_107
              apply False.elim assump_94


variable (p4 p2 p0 p6 p5 p1 p7 p3 : Prop)
theorem file30_131330 : (((((p2 → False) ∧ (False ∧ p6)) → ((p7 → p7) ∨ (p5 → False))) ∨ (((False → p4) ∧ (p1 → False)) ∧ ((p6 → False) → False))) ∧ ((((p6 ∧ False) → (p3 → p3)) → False) → (((p2 → False) → (p2 ∧ p2)) ∨ ((p0 → p2) ∧ (p5 → p3))))) := by
  apply And.intro
  apply Or.inl
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_21
    case intro assump_24 assump_25 =>
      apply False.elim assump_24
  intro assump_28
  apply Or.inl
  intro assump_31
  apply And.intro
  have assump_66 : ((p6 ∧ False) → (p3 → p3)) := by
    intro assump_36
    intro assump_37
    cases assump_36
    case intro assump_40 assump_41 =>
      apply False.elim assump_41
  let assump_35 := assump_28 assump_66
  apply False.elim assump_35
  have assump_67 : ((p6 ∧ False) → (p3 → p3)) := by
    intro assump_53
    intro assump_54
    cases assump_53
    case intro assump_57 assump_58 =>
      apply False.elim assump_58
  let assump_52 := assump_28 assump_67
  apply False.elim assump_52


variable (p1 p6 p7 p3 : Prop)
theorem file30_132379 : ((((((p3 → False) ∧ (False → p7)) ∨ ((p7 ∨ p1) ∧ (p6 ∧ False))) → (((p3 → p6) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_55 : ((((p3 → False) ∧ (False → p7)) ∨ ((p7 ∨ p1) ∧ (p6 ∧ False))) → (((p3 → p6) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        have assump_56 : (p3 → p6) := by
          intro assump_20
          have assump_57 : p3 := by
            exact assump_20
          let assump_25 := assump_11 assump_57
          apply False.elim assump_25
        let assump_19 := assump_6 assump_56
        apply False.elim assump_19
    case inr assump_10 =>
      cases assump_10
      case intro assump_32 assump_33 =>
        cases assump_32
        case inl assump_34 =>
          cases assump_33
          case intro assump_38 assump_39 =>
            apply False.elim assump_39
        case inr assump_35 =>
          cases assump_33
          case intro assump_46 assump_47 =>
            apply False.elim assump_47
  let assump_4 := assump_1 assump_55
  apply False.elim assump_4


variable (p1 p0 p2 p7 p4 p3 : Prop)
theorem file30_133589 : ((((((p2 → p0) → False) → ((False ∧ p1) → False)) ∨ (((p2 → p3) ∨ (True ∧ p4)) → False)) → ((((p7 ∧ True) ∧ (p4 → p4)) ∨ ((p1 ∨ p4) ∨ (p1 → p3))) → False)) → False) := by
  intro assump_1
  have assump_30 : ((((p2 → p0) → False) → ((False ∧ p1) → False)) ∨ (((p2 → p3) ∨ (True ∧ p4)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_30
  have assump_31 : (((p7 ∧ True) ∧ (p4 → p4)) ∨ ((p1 ∨ p4) ∨ (p1 → p3))) := by
    apply Or.inr
    apply Or.inr
    intro assump_12
    have assump_32 : ((((p2 → p0) → False) → ((False ∧ p1) → False)) ∨ (((p2 → p3) ∨ (True ∧ p4)) → False)) := by
      apply Or.inl
      intro assump_17
      intro assump_18
      cases assump_18
      case intro assump_19 assump_20 =>
        apply False.elim assump_19
    let assump_16 := assump_1 assump_32
    have assump_33 : (((p7 ∧ True) ∧ (p4 → p4)) ∨ ((p1 ∨ p4) ∨ (p1 → p3))) := by
      apply Or.inr
      apply Or.inl
      apply Or.inl
      exact assump_12
    let assump_23 := assump_16 assump_33
    apply False.elim assump_23
  let assump_11 := assump_4 assump_31
  apply False.elim assump_11


variable (p2 p7 p4 p1 p3 p6 p0 p5 : Prop)
theorem file30_134880 : (((((p1 ∨ p7) → (p4 ∨ p3)) → ((p6 → p6) ∨ (p5 ∨ p0))) ∨ (((p4 → p1) ∨ (p7 ∨ False)) ∧ ((p0 ∧ p4) ∨ (p1 ∨ False)))) ∨ ((((p2 → False) → (p0 ∧ p1)) → False) → (((p6 ∨ p7) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  exact assump_4


variable (p5 p3 p7 p4 : Prop)
theorem file30_135225 : (((((False → False) ∨ (False ∨ False)) → False) → False) ∨ ((((p4 → p5) → False) → False) ∨ (((p7 → False) → (p3 → False)) ∨ ((p4 → False) ∧ (p5 ∧ p4))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False → False) ∨ (False ∨ False)) := by
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p3 p2 p0 p5 p4 p6 : Prop)
theorem file30_135673 : (((((p3 ∨ p6) → (True → p7)) → ((False → p3) ∨ (p4 → p2))) ∨ (((p2 ∨ p6) ∨ (p4 ∨ p0)) → ((p3 ∨ p6) → False))) ∨ ((((p4 ∨ True) ∧ (True ∧ p4)) ∧ ((p5 → True) ∧ (p3 ∨ p0))) ∧ (((p4 ∧ p6) → False) ∧ ((p6 ∧ p6) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p3 p5 p7 p1 p0 p2 p4 p6 : Prop)
theorem file30_136071 : (((((True ∧ p4) ∨ (p7 ∨ p2)) ∨ ((p4 ∨ p3) ∧ (p7 ∨ p6))) → False) → ((((p6 ∨ p1) → (p3 ∨ True)) ∨ ((p1 → p5) ∧ (p7 ∨ p5))) ∨ (((p0 → False) ∧ (p6 → p4)) → ((p7 → False) → (p4 ∧ p2))))) := by
  intro assump_5
  apply Or.inl
  apply Or.inl
  intro assump_8
  cases assump_8
  case inl assump_9 =>
    apply Or.inr
    apply True.intro
  case inr assump_10 =>
    apply Or.inr
    apply True.intro


variable (p0 p7 p3 p1 : Prop)
theorem file30_136519 : (((((p7 ∨ p0) ∧ (p0 → False)) → ((True → False) → (p1 → p0))) ∧ (((p3 → False) ∧ (True → False)) ∧ ((p7 ∧ p1) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_21 : True := by
          apply True.intro
        let assump_17 := assump_9 assump_21
        apply False.elim assump_17


variable (p3 p7 p1 : Prop)
theorem file30_137030 : ((((((p1 ∨ False) → (False → False)) → False) → (((p1 → True) → False) ∨ ((p3 ∨ True) ∧ (p7 ∧ p3)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p1 ∨ False) → (False → False)) → False) → (((p1 → True) → False) ∨ ((p3 ∨ True) ∧ (p7 ∧ p3)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_24 : ((p1 ∨ False) → (False → False)) := by
      intro assump_13
      intro assump_14
      apply False.elim assump_14
    let assump_12 := assump_5 assump_24
    apply False.elim assump_12
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p1 p5 p0 p4 p7 p3 p2 : Prop)
theorem file30_137687 : ((((((p1 ∨ p5) → False) ∧ ((p2 → p2) ∧ (p7 → p1))) → (((p2 → True) ∨ (p1 ∨ True)) ∨ ((True → False) → False))) → ((((False → p4) ∧ (p3 ∧ p0)) → ((False → False) ∨ (p4 ∨ p1))) → False)) → False) := by
  intro assump_1
  have assump_35 : ((((p1 ∨ p5) → False) ∧ ((p2 → p2) ∧ (p7 → p1))) → (((p2 → True) ∨ (p1 ∨ True)) ∨ ((True → False) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply Or.inl
        intro assump_16
        apply True.intro
  let assump_4 := assump_1 assump_35
  have assump_36 : (((False → p4) ∧ (p3 ∧ p0)) → ((False → False) ∨ (p4 ∨ p1))) := by
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        apply Or.inl
        intro assump_29
        apply False.elim assump_29
  let assump_17 := assump_4 assump_36
  apply False.elim assump_17


variable (p3 p5 p2 p7 p4 p0 : Prop)
theorem file30_138734 : (((((False ∨ p7) ∧ (p5 ∧ p4)) ∨ ((False ∧ True) → (False ∧ True))) ∨ (((p3 → p2) ∧ (p7 → p4)) ∨ ((p3 → p3) ∧ (p5 → False)))) ∨ ((((p0 → False) → (p5 → False)) ∨ ((p7 → False) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_11
  apply And.intro
  cases assump_11
  case intro assump_12 assump_13 =>
    apply False.elim assump_12
  apply True.intro


variable (p4 p1 p6 p2 p7 p3 p5 : Prop)
theorem file30_139183 : ((((((p4 → p3) ∨ (p7 → p4)) → False) ∨ (((False → False) ∧ (p2 → False)) → False)) ∧ ((((p5 → p4) ∧ (p6 ∨ True)) ∨ ((p3 ∨ p3) → (True ∨ p1))) ∧ (((True ∨ False) → (p5 ∨ p5)) ∧ ((False → False) → False)))) → False) := by
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
          case intro assump_12 assump_13 =>
            cases assump_13
            case inl assump_16 =>
              cases assump_9
              case intro assump_20 assump_21 =>
                have assump_120 : (False → False) := by
                  intro assump_27
                  apply False.elim assump_27
                let assump_26 := assump_21 assump_120
                apply False.elim assump_26
            case inr assump_17 =>
              cases assump_9
              case intro assump_35 assump_36 =>
                have assump_121 : (False → False) := by
                  intro assump_42
                  apply False.elim assump_42
                let assump_41 := assump_36 assump_121
                apply False.elim assump_41
        case inr assump_11 =>
          cases assump_9
          case intro assump_50 assump_51 =>
            have assump_122 : (False → False) := by
              intro assump_57
              apply False.elim assump_57
            let assump_56 := assump_51 assump_122
            apply False.elim assump_56
    case inr assump_5 =>
      cases assump_3
      case intro assump_65 assump_66 =>
        cases assump_65
        case inl assump_67 =>
          cases assump_67
          case intro assump_69 assump_70 =>
            cases assump_70
            case inl assump_73 =>
              cases assump_66
              case intro assump_77 assump_78 =>
                have assump_123 : (False → False) := by
                  intro assump_84
                  apply False.elim assump_84
                let assump_83 := assump_78 assump_123
                apply False.elim assump_83
            case inr assump_74 =>
              cases assump_66
              case intro assump_92 assump_93 =>
                have assump_124 : (False → False) := by
                  intro assump_99
                  apply False.elim assump_99
                let assump_98 := assump_93 assump_124
                apply False.elim assump_98
        case inr assump_68 =>
          cases assump_66
          case intro assump_107 assump_108 =>
            have assump_125 : (False → False) := by
              intro assump_114
              apply False.elim assump_114
            let assump_113 := assump_108 assump_125
            apply False.elim assump_113


variable (p3 p6 p0 p1 p2 p5 p7 p4 : Prop)
theorem file30_142033 : (((((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) → False) → ((((False ∧ False) ∧ (p6 ∧ p4)) ∨ ((p0 → p0) ∨ (p2 ∨ p5))) → (((False → p3) ∨ (p7 → False)) → ((p3 ∧ p3) ∧ (p5 ∧ p6))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  apply And.intro
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
    case inr assump_9 =>
      cases assump_9
      case inl assump_16 =>
        have assump_792 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
          intro assump_23
          intro assump_24
          cases assump_24
          case intro assump_25 assump_26 =>
            cases assump_23
            case intro assump_31 assump_32 =>
              cases assump_31
              case intro assump_33 assump_34 =>
                have assump_793 : p5 := by
                  exact assump_26
                let assump_41 := assump_32 assump_793
                apply False.elim assump_41
        let assump_22 := assump_1 assump_792
        apply False.elim assump_22
      case inr assump_17 =>
        cases assump_17
        case inl assump_48 =>
          have assump_794 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
            intro assump_55
            intro assump_56
            cases assump_56
            case intro assump_57 assump_58 =>
              cases assump_55
              case intro assump_63 assump_64 =>
                cases assump_63
                case intro assump_65 assump_66 =>
                  have assump_795 : p5 := by
                    exact assump_58
                  let assump_73 := assump_64 assump_795
                  apply False.elim assump_73
          let assump_54 := assump_1 assump_794
          apply False.elim assump_54
        case inr assump_49 =>
          have assump_796 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
            intro assump_85
            intro assump_86
            cases assump_86
            case intro assump_87 assump_88 =>
              cases assump_85
              case intro assump_93 assump_94 =>
                cases assump_93
                case intro assump_95 assump_96 =>
                  have assump_797 : p5 := by
                    exact assump_88
                  let assump_103 := assump_94 assump_797
                  apply False.elim assump_103
          let assump_84 := assump_1 assump_796
          apply False.elim assump_84
  case inr assump_5 =>
    cases assump_2
    case inl assump_112 =>
      cases assump_112
      case intro assump_114 assump_115 =>
        cases assump_114
        case intro assump_116 assump_117 =>
          apply False.elim assump_116
    case inr assump_113 =>
      cases assump_113
      case inl assump_120 =>
        have assump_798 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
          intro assump_127
          intro assump_128
          cases assump_128
          case intro assump_129 assump_130 =>
            cases assump_127
            case intro assump_135 assump_136 =>
              cases assump_135
              case intro assump_137 assump_138 =>
                have assump_799 : p5 := by
                  exact assump_130
                let assump_145 := assump_136 assump_799
                apply False.elim assump_145
        let assump_126 := assump_1 assump_798
        apply False.elim assump_126
      case inr assump_121 =>
        cases assump_121
        case inl assump_152 =>
          have assump_800 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
            intro assump_159
            intro assump_160
            cases assump_160
            case intro assump_161 assump_162 =>
              cases assump_159
              case intro assump_167 assump_168 =>
                cases assump_167
                case intro assump_169 assump_170 =>
                  have assump_801 : p5 := by
                    exact assump_162
                  let assump_177 := assump_168 assump_801
                  apply False.elim assump_177
          let assump_158 := assump_1 assump_800
          apply False.elim assump_158
        case inr assump_153 =>
          have assump_802 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
            intro assump_189
            intro assump_190
            cases assump_190
            case intro assump_191 assump_192 =>
              cases assump_189
              case intro assump_197 assump_198 =>
                cases assump_197
                case intro assump_199 assump_200 =>
                  have assump_803 : p5 := by
                    exact assump_192
                  let assump_207 := assump_198 assump_803
                  apply False.elim assump_207
          let assump_188 := assump_1 assump_802
          apply False.elim assump_188
  cases assump_3
  case inl assump_214 =>
    cases assump_2
    case inl assump_218 =>
      cases assump_218
      case intro assump_220 assump_221 =>
        cases assump_220
        case intro assump_222 assump_223 =>
          apply False.elim assump_222
    case inr assump_219 =>
      cases assump_219
      case inl assump_226 =>
        have assump_804 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
          intro assump_233
          intro assump_234
          cases assump_234
          case intro assump_235 assump_236 =>
            cases assump_233
            case intro assump_241 assump_242 =>
              cases assump_241
              case intro assump_243 assump_244 =>
                have assump_805 : p5 := by
                  exact assump_236
                let assump_251 := assump_242 assump_805
                apply False.elim assump_251
        let assump_232 := assump_1 assump_804
        apply False.elim assump_232
      case inr assump_227 =>
        cases assump_227
        case inl assump_258 =>
          have assump_806 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
            intro assump_265
            intro assump_266
            cases assump_266
            case intro assump_267 assump_268 =>
              cases assump_265
              case intro assump_273 assump_274 =>
                cases assump_273
                case intro assump_275 assump_276 =>
                  have assump_807 : p5 := by
                    exact assump_268
                  let assump_283 := assump_274 assump_807
                  apply False.elim assump_283
          let assump_264 := assump_1 assump_806
          apply False.elim assump_264
        case inr assump_259 =>
          have assump_808 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
            intro assump_295
            intro assump_296
            cases assump_296
            case intro assump_297 assump_298 =>
              cases assump_295
              case intro assump_303 assump_304 =>
                cases assump_303
                case intro assump_305 assump_306 =>
                  have assump_809 : p5 := by
                    exact assump_298
                  let assump_313 := assump_304 assump_809
                  apply False.elim assump_313
          let assump_294 := assump_1 assump_808
          apply False.elim assump_294
  case inr assump_215 =>
    cases assump_2
    case inl assump_322 =>
      cases assump_322
      case intro assump_324 assump_325 =>
        cases assump_324
        case intro assump_326 assump_327 =>
          apply False.elim assump_326
    case inr assump_323 =>
      cases assump_323
      case inl assump_330 =>
        have assump_810 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
          intro assump_337
          intro assump_338
          cases assump_338
          case intro assump_339 assump_340 =>
            cases assump_337
            case intro assump_345 assump_346 =>
              cases assump_345
              case intro assump_347 assump_348 =>
                have assump_811 : p5 := by
                  exact assump_340
                let assump_355 := assump_346 assump_811
                apply False.elim assump_355
        let assump_336 := assump_1 assump_810
        apply False.elim assump_336
      case inr assump_331 =>
        cases assump_331
        case inl assump_362 =>
          have assump_812 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
            intro assump_369
            intro assump_370
            cases assump_370
            case intro assump_371 assump_372 =>
              cases assump_369
              case intro assump_377 assump_378 =>
                cases assump_377
                case intro assump_379 assump_380 =>
                  have assump_813 : p5 := by
                    exact assump_372
                  let assump_387 := assump_378 assump_813
                  apply False.elim assump_387
          let assump_368 := assump_1 assump_812
          apply False.elim assump_368
        case inr assump_363 =>
          have assump_814 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
            intro assump_399
            intro assump_400
            cases assump_400
            case intro assump_401 assump_402 =>
              cases assump_399
              case intro assump_407 assump_408 =>
                cases assump_407
                case intro assump_409 assump_410 =>
                  have assump_815 : p5 := by
                    exact assump_402
                  let assump_417 := assump_408 assump_815
                  apply False.elim assump_417
          let assump_398 := assump_1 assump_814
          apply False.elim assump_398
  apply And.intro
  cases assump_3
  case inl assump_424 =>
    cases assump_2
    case inl assump_428 =>
      cases assump_428
      case intro assump_430 assump_431 =>
        cases assump_430
        case intro assump_432 assump_433 =>
          apply False.elim assump_432
    case inr assump_429 =>
      cases assump_429
      case inl assump_436 =>
        have assump_816 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
          intro assump_443
          intro assump_444
          cases assump_444
          case intro assump_445 assump_446 =>
            cases assump_443
            case intro assump_451 assump_452 =>
              cases assump_451
              case intro assump_453 assump_454 =>
                have assump_817 : p5 := by
                  exact assump_446
                let assump_461 := assump_452 assump_817
                apply False.elim assump_461
        let assump_442 := assump_1 assump_816
        apply False.elim assump_442
      case inr assump_437 =>
        cases assump_437
        case inl assump_468 =>
          have assump_818 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
            intro assump_475
            intro assump_476
            cases assump_476
            case intro assump_477 assump_478 =>
              cases assump_475
              case intro assump_483 assump_484 =>
                cases assump_483
                case intro assump_485 assump_486 =>
                  have assump_819 : p5 := by
                    exact assump_478
                  let assump_493 := assump_484 assump_819
                  apply False.elim assump_493
          let assump_474 := assump_1 assump_818
          apply False.elim assump_474
        case inr assump_469 =>
          exact assump_469
  case inr assump_425 =>
    cases assump_2
    case inl assump_506 =>
      cases assump_506
      case intro assump_508 assump_509 =>
        cases assump_508
        case intro assump_510 assump_511 =>
          apply False.elim assump_510
    case inr assump_507 =>
      cases assump_507
      case inl assump_514 =>
        have assump_820 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
          intro assump_521
          intro assump_522
          cases assump_522
          case intro assump_523 assump_524 =>
            cases assump_521
            case intro assump_529 assump_530 =>
              cases assump_529
              case intro assump_531 assump_532 =>
                have assump_821 : p5 := by
                  exact assump_524
                let assump_539 := assump_530 assump_821
                apply False.elim assump_539
        let assump_520 := assump_1 assump_820
        apply False.elim assump_520
      case inr assump_515 =>
        cases assump_515
        case inl assump_546 =>
          have assump_822 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
            intro assump_553
            intro assump_554
            cases assump_554
            case intro assump_555 assump_556 =>
              cases assump_553
              case intro assump_561 assump_562 =>
                cases assump_561
                case intro assump_563 assump_564 =>
                  have assump_823 : p5 := by
                    exact assump_556
                  let assump_571 := assump_562 assump_823
                  apply False.elim assump_571
          let assump_552 := assump_1 assump_822
          apply False.elim assump_552
        case inr assump_547 =>
          exact assump_547
  cases assump_3
  case inl assump_582 =>
    cases assump_2
    case inl assump_586 =>
      cases assump_586
      case intro assump_588 assump_589 =>
        cases assump_588
        case intro assump_590 assump_591 =>
          apply False.elim assump_590
    case inr assump_587 =>
      cases assump_587
      case inl assump_594 =>
        have assump_824 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
          intro assump_601
          intro assump_602
          cases assump_602
          case intro assump_603 assump_604 =>
            cases assump_601
            case intro assump_609 assump_610 =>
              cases assump_609
              case intro assump_611 assump_612 =>
                have assump_825 : p5 := by
                  exact assump_604
                let assump_619 := assump_610 assump_825
                apply False.elim assump_619
        let assump_600 := assump_1 assump_824
        apply False.elim assump_600
      case inr assump_595 =>
        cases assump_595
        case inl assump_626 =>
          have assump_826 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
            intro assump_633
            intro assump_634
            cases assump_634
            case intro assump_635 assump_636 =>
              cases assump_633
              case intro assump_641 assump_642 =>
                cases assump_641
                case intro assump_643 assump_644 =>
                  have assump_827 : p5 := by
                    exact assump_636
                  let assump_651 := assump_642 assump_827
                  apply False.elim assump_651
          let assump_632 := assump_1 assump_826
          apply False.elim assump_632
        case inr assump_627 =>
          have assump_828 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
            intro assump_663
            intro assump_664
            cases assump_664
            case intro assump_665 assump_666 =>
              cases assump_663
              case intro assump_671 assump_672 =>
                cases assump_671
                case intro assump_673 assump_674 =>
                  have assump_829 : p5 := by
                    exact assump_666
                  let assump_681 := assump_672 assump_829
                  apply False.elim assump_681
          let assump_662 := assump_1 assump_828
          apply False.elim assump_662
  case inr assump_583 =>
    cases assump_2
    case inl assump_690 =>
      cases assump_690
      case intro assump_692 assump_693 =>
        cases assump_692
        case intro assump_694 assump_695 =>
          apply False.elim assump_694
    case inr assump_691 =>
      cases assump_691
      case inl assump_698 =>
        have assump_830 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
          intro assump_705
          intro assump_706
          cases assump_706
          case intro assump_707 assump_708 =>
            cases assump_705
            case intro assump_713 assump_714 =>
              cases assump_713
              case intro assump_715 assump_716 =>
                have assump_831 : p5 := by
                  exact assump_708
                let assump_723 := assump_714 assump_831
                apply False.elim assump_723
        let assump_704 := assump_1 assump_830
        apply False.elim assump_704
      case inr assump_699 =>
        cases assump_699
        case inl assump_730 =>
          have assump_832 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
            intro assump_737
            intro assump_738
            cases assump_738
            case intro assump_739 assump_740 =>
              cases assump_737
              case intro assump_745 assump_746 =>
                cases assump_745
                case intro assump_747 assump_748 =>
                  have assump_833 : p5 := by
                    exact assump_740
                  let assump_755 := assump_746 assump_833
                  apply False.elim assump_755
          let assump_736 := assump_1 assump_832
          apply False.elim assump_736
        case inr assump_731 =>
          have assump_834 : (((p1 ∧ True) ∧ (p5 → False)) → ((p1 ∧ p5) → False)) := by
            intro assump_767
            intro assump_768
            cases assump_768
            case intro assump_769 assump_770 =>
              cases assump_767
              case intro assump_775 assump_776 =>
                cases assump_775
                case intro assump_777 assump_778 =>
                  have assump_835 : p5 := by
                    exact assump_770
                  let assump_785 := assump_776 assump_835
                  apply False.elim assump_785
          let assump_766 := assump_1 assump_834
          apply False.elim assump_766


variable (p4 p2 p0 p6 p5 p7 p3 p1 : Prop)
theorem file30_160231 : (((((p2 → False) → False) → ((p2 ∨ p0) ∨ (p4 → False))) → (((p0 → False) ∧ (p3 → False)) → ((p6 ∧ p7) → False))) → ((((p5 ∧ p2) ∧ (p0 ∨ True)) → ((p2 ∨ p0) ∧ (False → False))) ∨ (((p4 ∧ True) ∧ (True ∧ p1)) ∧ ((p2 ∨ p7) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case inl assump_13 =>
        apply Or.inl
        exact assump_8
      case inr assump_14 =>
        apply Or.inl
        exact assump_8
  intro assump_19
  apply False.elim assump_19


variable (p5 p7 p0 p1 p2 p4 p3 p6 : Prop)
theorem file30_160920 : (((((p7 → False) → (p4 ∨ p6)) → ((True ∧ p3) ∨ (False → False))) ∨ (((p0 ∧ p4) ∨ (p7 → False)) ∧ ((p7 → p3) ∧ (p3 → False)))) ∨ ((((p7 ∧ p6) ∧ (p5 → False)) ∨ ((p1 ∧ p3) → (p2 → False))) ∧ (((p0 → p0) ∨ (p6 ∨ p4)) ∨ ((p6 ∨ p6) ∨ (False ∧ p0))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  apply False.elim assump_4


variable (p4 p6 p1 p7 p2 p0 p3 p5 : Prop)
theorem file30_161345 : (((((p0 ∨ p5) → False) ∧ ((False ∨ p3) ∧ (p1 ∨ p4))) → False) → ((((p2 → False) ∨ (p1 → p3)) → ((True → False) → False)) ∨ (((p7 → p6) ∧ (p5 ∧ p5)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    have assump_24 : True := by
      apply True.intro
    let assump_13 := assump_5 assump_24
    apply False.elim assump_13
  case inr assump_9 =>
    have assump_25 : True := by
      apply True.intro
    let assump_20 := assump_5 assump_25
    apply False.elim assump_20


variable (p3 p5 p0 p7 p2 : Prop)
theorem file30_161948 : (((((p7 ∧ p3) ∧ (p3 → False)) ∨ ((p2 ∨ p0) ∧ (False → False))) ∧ (((p5 ∧ False) ∨ (True ∧ False)) ∧ ((p7 → False) ∨ (p5 ∨ p7)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                apply False.elim assump_21
            case inr assump_19 =>
              cases assump_19
              case intro assump_26 assump_27 =>
                apply False.elim assump_27
    case inr assump_5 =>
      cases assump_5
      case intro assump_32 assump_33 =>
        cases assump_32
        case inl assump_34 =>
          cases assump_3
          case intro assump_40 assump_41 =>
            cases assump_40
            case inl assump_42 =>
              cases assump_42
              case intro assump_44 assump_45 =>
                apply False.elim assump_45
            case inr assump_43 =>
              cases assump_43
              case intro assump_50 assump_51 =>
                apply False.elim assump_51
        case inr assump_35 =>
          cases assump_3
          case intro assump_60 assump_61 =>
            cases assump_60
            case inl assump_62 =>
              cases assump_62
              case intro assump_64 assump_65 =>
                apply False.elim assump_65
            case inr assump_63 =>
              cases assump_63
              case intro assump_70 assump_71 =>
                apply False.elim assump_71


variable (p0 p2 p6 p1 p7 p5 : Prop)
theorem file30_163777 : ((((((p2 ∨ True) ∨ (p0 ∧ p1)) ∨ ((p7 ∨ p2) ∧ (False → False))) ∨ (((p5 → p1) ∨ (p1 → p1)) ∧ ((False ∧ p5) → (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p2 ∨ True) ∨ (p0 ∧ p1)) ∨ ((p7 ∨ p2) ∧ (False → False))) ∨ (((p5 → p1) ∨ (p1 → p1)) ∧ ((False ∧ p5) → (p6 → False)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p7 p5 p3 p4 p6 p1 p2 : Prop)
theorem file30_164304 : (((((p4 ∧ p6) → False) → ((False ∧ p1) ∨ (p6 ∨ p2))) → (((p6 → p1) → (p7 → p7)) → False)) → ((((p2 ∧ p4) → False) ∧ ((True → True) → (p2 → False))) ∨ (((p1 → False) → False) → ((p5 → False) → (p3 → False))))) := by
  intro assump_5
  apply Or.inl
  apply And.intro
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    have assump_54 : (((p4 ∧ p6) → False) → ((False ∧ p1) ∨ (p6 ∨ p2))) := by
      intro assump_18
      apply Or.inr
      apply Or.inr
      exact assump_9
    let assump_17 := assump_5 assump_54
    have assump_55 : ((p6 → p1) → (p7 → p7)) := by
      intro assump_22
      intro assump_23
      exact assump_23
    let assump_21 := assump_17 assump_55
    apply False.elim assump_21
  intro assump_31
  intro assump_32
  have assump_56 : (((p4 ∧ p6) → False) → ((False ∧ p1) ∨ (p6 ∨ p2))) := by
    intro assump_41
    apply Or.inr
    apply Or.inr
    exact assump_32
  let assump_40 := assump_5 assump_56
  have assump_57 : ((p6 → p1) → (p7 → p7)) := by
    intro assump_45
    intro assump_46
    exact assump_46
  let assump_44 := assump_40 assump_57
  apply False.elim assump_44


variable (p1 p0 p2 p4 p5 p3 p6 : Prop)
theorem file30_165490 : ((((((p0 ∧ p4) ∧ (p3 ∧ p1)) ∨ ((p5 ∧ True) → False)) → (((p6 ∧ False) → (p3 → p6)) ∨ ((p2 → False) ∧ (p4 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_47 : ((((p0 ∧ p4) ∧ (p3 ∧ p1)) ∨ ((p5 ∧ True) → False)) → (((p6 ∧ False) → (p3 → p6)) ∨ ((p2 → False) ∧ (p4 ∧ False)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            apply Or.inl
            intro assump_22
            intro assump_23
            cases assump_22
            case intro assump_26 assump_27 =>
              apply False.elim assump_27
    case inr assump_7 =>
      apply Or.inl
      intro assump_34
      intro assump_35
      cases assump_34
      case intro assump_38 assump_39 =>
        apply False.elim assump_39
  let assump_4 := assump_1 assump_47
  apply False.elim assump_4


variable (p0 p2 p7 : Prop)
theorem file30_166541 : (((((p7 ∨ True) → False) → ((False ∧ p2) ∨ (True → p0))) → False) → False) := by
  intro assump_1
  have assump_18 : (((p7 ∨ True) → False) → ((False ∧ p2) ∨ (True → p0))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    have assump_19 : (p7 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p7 p2 p4 p0 : Prop)
theorem file30_167048 : ((((((p4 → False) → (p2 → False)) ∨ ((p2 ∨ p2) → (p7 → p0))) → False) ∧ ((((p2 ∧ p3) → False) → ((True → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_23 : (((p2 ∧ p3) → False) → ((True → False) → False)) := by
      intro assump_9
      intro assump_10
      have assump_24 : True := by
        apply True.intro
      let assump_16 := assump_10 assump_24
      apply False.elim assump_16
    let assump_8 := assump_3 assump_23
    apply False.elim assump_8


variable (p7 p1 p0 p4 p6 p3 p5 p2 : Prop)
theorem file30_167652 : (((((False → p4) ∧ (False → p3)) ∧ ((p4 → False) ∧ (p7 → False))) ∧ (((p5 ∧ p3) → (p0 → False)) ∧ ((False → False) → False))) → ((((p6 → False) ∨ (True → p1)) ∨ ((p1 ∨ p1) ∨ (p1 ∨ p2))) → (((p3 ∨ p1) ∧ (p7 ∨ p5)) ∧ ((p0 → False) → (p6 ∧ p5))))) := by
  intro assump_10
  intro assump_11
  apply And.intro
  apply And.intro
  cases assump_11
  case inl assump_12 =>
    cases assump_12
    case inl assump_14 =>
      cases assump_10
      case intro assump_18 assump_19 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          cases assump_20
          case intro assump_22 assump_23 =>
            cases assump_21
            case intro assump_28 assump_29 =>
              cases assump_19
              case intro assump_34 assump_35 =>
                have assump_780 : (False → False) := by
                  intro assump_41
                  apply False.elim assump_41
                let assump_40 := assump_35 assump_780
                apply False.elim assump_40
    case inr assump_15 =>
      cases assump_10
      case intro assump_49 assump_50 =>
        cases assump_49
        case intro assump_51 assump_52 =>
          cases assump_51
          case intro assump_53 assump_54 =>
            cases assump_52
            case intro assump_59 assump_60 =>
              cases assump_50
              case intro assump_65 assump_66 =>
                have assump_781 : (False → False) := by
                  intro assump_72
                  apply False.elim assump_72
                let assump_71 := assump_66 assump_781
                apply False.elim assump_71
  case inr assump_13 =>
    cases assump_13
    case inl assump_78 =>
      cases assump_78
      case inl assump_80 =>
        cases assump_10
        case intro assump_84 assump_85 =>
          cases assump_84
          case intro assump_86 assump_87 =>
            cases assump_86
            case intro assump_88 assump_89 =>
              cases assump_87
              case intro assump_94 assump_95 =>
                cases assump_85
                case intro assump_100 assump_101 =>
                  apply Or.inr
                  exact assump_80
      case inr assump_81 =>
        cases assump_10
        case intro assump_108 assump_109 =>
          cases assump_108
          case intro assump_110 assump_111 =>
            cases assump_110
            case intro assump_112 assump_113 =>
              cases assump_111
              case intro assump_118 assump_119 =>
                cases assump_109
                case intro assump_124 assump_125 =>
                  apply Or.inr
                  exact assump_81
    case inr assump_79 =>
      cases assump_79
      case inl assump_130 =>
        cases assump_10
        case intro assump_134 assump_135 =>
          cases assump_134
          case intro assump_136 assump_137 =>
            cases assump_136
            case intro assump_138 assump_139 =>
              cases assump_137
              case intro assump_144 assump_145 =>
                cases assump_135
                case intro assump_150 assump_151 =>
                  apply Or.inr
                  exact assump_130
      case inr assump_131 =>
        cases assump_10
        case intro assump_158 assump_159 =>
          cases assump_158
          case intro assump_160 assump_161 =>
            cases assump_160
            case intro assump_162 assump_163 =>
              cases assump_161
              case intro assump_168 assump_169 =>
                cases assump_159
                case intro assump_174 assump_175 =>
                  have assump_782 : (False → False) := by
                    intro assump_181
                    apply False.elim assump_181
                  let assump_180 := assump_175 assump_782
                  apply False.elim assump_180
  cases assump_11
  case inl assump_187 =>
    cases assump_187
    case inl assump_189 =>
      cases assump_10
      case intro assump_193 assump_194 =>
        cases assump_193
        case intro assump_195 assump_196 =>
          cases assump_195
          case intro assump_197 assump_198 =>
            cases assump_196
            case intro assump_203 assump_204 =>
              cases assump_194
              case intro assump_209 assump_210 =>
                have assump_783 : (False → False) := by
                  intro assump_216
                  apply False.elim assump_216
                let assump_215 := assump_210 assump_783
                apply False.elim assump_215
    case inr assump_190 =>
      cases assump_10
      case intro assump_224 assump_225 =>
        cases assump_224
        case intro assump_226 assump_227 =>
          cases assump_226
          case intro assump_228 assump_229 =>
            cases assump_227
            case intro assump_234 assump_235 =>
              cases assump_225
              case intro assump_240 assump_241 =>
                have assump_784 : (False → False) := by
                  intro assump_247
                  apply False.elim assump_247
                let assump_246 := assump_241 assump_784
                apply False.elim assump_246
  case inr assump_188 =>
    cases assump_188
    case inl assump_253 =>
      cases assump_253
      case inl assump_255 =>
        cases assump_10
        case intro assump_259 assump_260 =>
          cases assump_259
          case intro assump_261 assump_262 =>
            cases assump_261
            case intro assump_263 assump_264 =>
              cases assump_262
              case intro assump_269 assump_270 =>
                cases assump_260
                case intro assump_275 assump_276 =>
                  have assump_785 : (False → False) := by
                    intro assump_282
                    apply False.elim assump_282
                  let assump_281 := assump_276 assump_785
                  apply False.elim assump_281
      case inr assump_256 =>
        cases assump_10
        case intro assump_290 assump_291 =>
          cases assump_290
          case intro assump_292 assump_293 =>
            cases assump_292
            case intro assump_294 assump_295 =>
              cases assump_293
              case intro assump_300 assump_301 =>
                cases assump_291
                case intro assump_306 assump_307 =>
                  have assump_786 : (False → False) := by
                    intro assump_313
                    apply False.elim assump_313
                  let assump_312 := assump_307 assump_786
                  apply False.elim assump_312
    case inr assump_254 =>
      cases assump_254
      case inl assump_319 =>
        cases assump_10
        case intro assump_323 assump_324 =>
          cases assump_323
          case intro assump_325 assump_326 =>
            cases assump_325
            case intro assump_327 assump_328 =>
              cases assump_326
              case intro assump_333 assump_334 =>
                cases assump_324
                case intro assump_339 assump_340 =>
                  have assump_787 : (False → False) := by
                    intro assump_346
                    apply False.elim assump_346
                  let assump_345 := assump_340 assump_787
                  apply False.elim assump_345
      case inr assump_320 =>
        cases assump_10
        case intro assump_354 assump_355 =>
          cases assump_354
          case intro assump_356 assump_357 =>
            cases assump_356
            case intro assump_358 assump_359 =>
              cases assump_357
              case intro assump_364 assump_365 =>
                cases assump_355
                case intro assump_370 assump_371 =>
                  have assump_788 : (False → False) := by
                    intro assump_377
                    apply False.elim assump_377
                  let assump_376 := assump_371 assump_788
                  apply False.elim assump_376
  intro assump_383
  apply And.intro
  cases assump_11
  case inl assump_386 =>
    cases assump_386
    case inl assump_388 =>
      cases assump_10
      case intro assump_392 assump_393 =>
        cases assump_392
        case intro assump_394 assump_395 =>
          cases assump_394
          case intro assump_396 assump_397 =>
            cases assump_395
            case intro assump_402 assump_403 =>
              cases assump_393
              case intro assump_408 assump_409 =>
                have assump_789 : (False → False) := by
                  intro assump_415
                  apply False.elim assump_415
                let assump_414 := assump_409 assump_789
                apply False.elim assump_414
    case inr assump_389 =>
      cases assump_10
      case intro assump_423 assump_424 =>
        cases assump_423
        case intro assump_425 assump_426 =>
          cases assump_425
          case intro assump_427 assump_428 =>
            cases assump_426
            case intro assump_433 assump_434 =>
              cases assump_424
              case intro assump_439 assump_440 =>
                have assump_790 : (False → False) := by
                  intro assump_446
                  apply False.elim assump_446
                let assump_445 := assump_440 assump_790
                apply False.elim assump_445
  case inr assump_387 =>
    cases assump_387
    case inl assump_452 =>
      cases assump_452
      case inl assump_454 =>
        cases assump_10
        case intro assump_458 assump_459 =>
          cases assump_458
          case intro assump_460 assump_461 =>
            cases assump_460
            case intro assump_462 assump_463 =>
              cases assump_461
              case intro assump_468 assump_469 =>
                cases assump_459
                case intro assump_474 assump_475 =>
                  have assump_791 : (False → False) := by
                    intro assump_481
                    apply False.elim assump_481
                  let assump_480 := assump_475 assump_791
                  apply False.elim assump_480
      case inr assump_455 =>
        cases assump_10
        case intro assump_489 assump_490 =>
          cases assump_489
          case intro assump_491 assump_492 =>
            cases assump_491
            case intro assump_493 assump_494 =>
              cases assump_492
              case intro assump_499 assump_500 =>
                cases assump_490
                case intro assump_505 assump_506 =>
                  have assump_792 : (False → False) := by
                    intro assump_512
                    apply False.elim assump_512
                  let assump_511 := assump_506 assump_792
                  apply False.elim assump_511
    case inr assump_453 =>
      cases assump_453
      case inl assump_518 =>
        cases assump_10
        case intro assump_522 assump_523 =>
          cases assump_522
          case intro assump_524 assump_525 =>
            cases assump_524
            case intro assump_526 assump_527 =>
              cases assump_525
              case intro assump_532 assump_533 =>
                cases assump_523
                case intro assump_538 assump_539 =>
                  have assump_793 : (False → False) := by
                    intro assump_545
                    apply False.elim assump_545
                  let assump_544 := assump_539 assump_793
                  apply False.elim assump_544
      case inr assump_519 =>
        cases assump_10
        case intro assump_553 assump_554 =>
          cases assump_553
          case intro assump_555 assump_556 =>
            cases assump_555
            case intro assump_557 assump_558 =>
              cases assump_556
              case intro assump_563 assump_564 =>
                cases assump_554
                case intro assump_569 assump_570 =>
                  have assump_794 : (False → False) := by
                    intro assump_576
                    apply False.elim assump_576
                  let assump_575 := assump_570 assump_794
                  apply False.elim assump_575
  cases assump_11
  case inl assump_584 =>
    cases assump_584
    case inl assump_586 =>
      cases assump_10
      case intro assump_590 assump_591 =>
        cases assump_590
        case intro assump_592 assump_593 =>
          cases assump_592
          case intro assump_594 assump_595 =>
            cases assump_593
            case intro assump_600 assump_601 =>
              cases assump_591
              case intro assump_606 assump_607 =>
                have assump_795 : (False → False) := by
                  intro assump_613
                  apply False.elim assump_613
                let assump_612 := assump_607 assump_795
                apply False.elim assump_612
    case inr assump_587 =>
      cases assump_10
      case intro assump_621 assump_622 =>
        cases assump_621
        case intro assump_623 assump_624 =>
          cases assump_623
          case intro assump_625 assump_626 =>
            cases assump_624
            case intro assump_631 assump_632 =>
              cases assump_622
              case intro assump_637 assump_638 =>
                have assump_796 : (False → False) := by
                  intro assump_644
                  apply False.elim assump_644
                let assump_643 := assump_638 assump_796
                apply False.elim assump_643
  case inr assump_585 =>
    cases assump_585
    case inl assump_650 =>
      cases assump_650
      case inl assump_652 =>
        cases assump_10
        case intro assump_656 assump_657 =>
          cases assump_656
          case intro assump_658 assump_659 =>
            cases assump_658
            case intro assump_660 assump_661 =>
              cases assump_659
              case intro assump_666 assump_667 =>
                cases assump_657
                case intro assump_672 assump_673 =>
                  have assump_797 : (False → False) := by
                    intro assump_679
                    apply False.elim assump_679
                  let assump_678 := assump_673 assump_797
                  apply False.elim assump_678
      case inr assump_653 =>
        cases assump_10
        case intro assump_687 assump_688 =>
          cases assump_687
          case intro assump_689 assump_690 =>
            cases assump_689
            case intro assump_691 assump_692 =>
              cases assump_690
              case intro assump_697 assump_698 =>
                cases assump_688
                case intro assump_703 assump_704 =>
                  have assump_798 : (False → False) := by
                    intro assump_710
                    apply False.elim assump_710
                  let assump_709 := assump_704 assump_798
                  apply False.elim assump_709
    case inr assump_651 =>
      cases assump_651
      case inl assump_716 =>
        cases assump_10
        case intro assump_720 assump_721 =>
          cases assump_720
          case intro assump_722 assump_723 =>
            cases assump_722
            case intro assump_724 assump_725 =>
              cases assump_723
              case intro assump_730 assump_731 =>
                cases assump_721
                case intro assump_736 assump_737 =>
                  have assump_799 : (False → False) := by
                    intro assump_743
                    apply False.elim assump_743
                  let assump_742 := assump_737 assump_799
                  apply False.elim assump_742
      case inr assump_717 =>
        cases assump_10
        case intro assump_751 assump_752 =>
          cases assump_751
          case intro assump_753 assump_754 =>
            cases assump_753
            case intro assump_755 assump_756 =>
              cases assump_754
              case intro assump_761 assump_762 =>
                cases assump_752
                case intro assump_767 assump_768 =>
                  have assump_800 : (False → False) := by
                    intro assump_774
                    apply False.elim assump_774
                  let assump_773 := assump_768 assump_800
                  apply False.elim assump_773


