variable (p5 p1 p6 p4 p2 p0 : Prop)
theorem file96_44 : ((((((p1 → True) ∧ (p4 ∧ p6)) ∨ ((p2 ∧ p2) ∨ (p2 → p0))) ∨ (((p1 → False) → False) → ((True → False) ∨ (p2 ∧ p5)))) → False) → False) := by
  intro assump_5
  have assump_22 : ((((p1 → True) ∧ (p4 ∧ p6)) ∨ ((p2 ∧ p2) ∨ (p2 → p0))) ∨ (((p1 → False) → False) → ((True → False) ∨ (p2 ∧ p5)))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    intro assump_10
    have assump_23 : ((((p1 → True) ∧ (p4 ∧ p6)) ∨ ((p2 ∧ p2) ∨ (p2 → p0))) ∨ (((p1 → False) → False) → ((True → False) ∨ (p2 ∧ p5)))) := by
      apply Or.inl
      apply Or.inr
      apply Or.inl
      apply And.intro
      exact assump_10
      exact assump_10
    let assump_14 := assump_5 assump_23
    apply False.elim assump_14
  let assump_8 := assump_5 assump_22
  apply False.elim assump_8


variable (p4 p1 p6 p5 p0 p7 : Prop)
theorem file96_871 : (((((p1 → p1) → False) ∧ ((False ∨ False) ∨ (p5 ∨ p4))) → (((p6 → p7) ∧ (p7 ∨ p7)) → False)) ∧ ((((p0 ∨ p0) → (p0 ∨ p0)) → False) → False)) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_12
        case inl assump_15 =>
          cases assump_15
          case inl assump_17 =>
            apply False.elim assump_17
          case inr assump_18 =>
            apply False.elim assump_18
        case inr assump_16 =>
          cases assump_16
          case inl assump_23 =>
            have assump_95 : (p1 → p1) := by
              intro assump_29
              exact assump_29
            let assump_28 := assump_11 assump_95
            apply False.elim assump_28
          case inr assump_24 =>
            have assump_96 : (p1 → p1) := by
              intro assump_39
              exact assump_39
            let assump_38 := assump_11 assump_96
            apply False.elim assump_38
    case inr assump_8 =>
      cases assump_1
      case intro assump_47 assump_48 =>
        cases assump_48
        case inl assump_51 =>
          cases assump_51
          case inl assump_53 =>
            apply False.elim assump_53
          case inr assump_54 =>
            apply False.elim assump_54
        case inr assump_52 =>
          cases assump_52
          case inl assump_59 =>
            have assump_97 : (p1 → p1) := by
              intro assump_65
              exact assump_65
            let assump_64 := assump_47 assump_97
            apply False.elim assump_64
          case inr assump_60 =>
            have assump_98 : (p1 → p1) := by
              intro assump_75
              exact assump_75
            let assump_74 := assump_47 assump_98
            apply False.elim assump_74
  intro assump_81
  have assump_99 : ((p0 ∨ p0) → (p0 ∨ p0)) := by
    intro assump_85
    cases assump_85
    case inl assump_86 =>
      apply Or.inl
      exact assump_86
    case inr assump_87 =>
      apply Or.inl
      exact assump_87
  let assump_84 := assump_81 assump_99
  apply False.elim assump_84


variable (p2 p6 p3 p1 : Prop)
theorem file96_3130 : ((((((False → False) → False) → False) ∨ (((p3 ∧ p6) → False) → ((p1 ∧ p2) ∨ (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) → False) → False) ∨ (((p3 ∧ p6) → False) → ((p1 ∧ p2) ∨ (p6 → False)))) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p6 p1 p0 p2 p3 : Prop)
theorem file96_3706 : (((((p1 ∧ False) ∧ (p1 ∨ p1)) ∧ ((p0 → p5) → (False ∨ p5))) ∧ (((p5 ∧ p1) ∨ (p0 → False)) ∨ ((p3 → False) ∨ (p1 → False)))) → ((((True ∨ True) ∧ (p5 → p1)) → False) → (((True ∧ p6) → (p6 ∧ False)) → ((p2 → True) → (p6 ∨ p3))))) := by
  intro assump_8
  intro assump_9
  intro assump_10
  intro assump_11
  cases assump_8
  case intro assump_18 assump_19 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          apply False.elim assump_25


variable (p7 p6 p4 p1 p3 p5 : Prop)
theorem file96_4346 : ((((((p6 → False) ∨ (p5 ∧ p7)) → ((p4 ∨ p3) → (p7 → False))) → False) ∧ ((((p4 ∨ True) ∨ (p3 → False)) ∨ ((p3 ∨ p5) → (p1 ∨ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_12 : (((p4 ∨ True) ∨ (p3 → False)) ∨ ((p3 ∨ p5) → (p1 ∨ p6))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_12
    apply False.elim assump_8


variable (p3 p1 p2 p7 p6 p5 p0 p4 : Prop)
theorem file96_4868 : ((((((p7 → True) → False) → ((p7 → p1) ∧ (p4 → False))) ∧ (((p1 → p4) → (False ∨ False)) → ((p5 ∨ p7) ∧ (p4 → p6)))) ∧ ((((False ∧ p5) → False) → False) ∧ (((p0 ∧ p7) ∧ (p7 → p5)) → ((p1 ∨ p2) ∧ (p3 ∧ p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        have assump_26 : ((False ∧ p5) → False) := by
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            apply False.elim assump_19
        let assump_17 := assump_10 assump_26
        apply False.elim assump_17


variable (p5 p3 p0 p7 p6 : Prop)
theorem file96_5602 : (((((p5 → p7) → (True ∨ p0)) → False) → (((p7 → False) → (p5 → p3)) → ((p7 ∧ p0) → False))) ∧ ((((False → False) → (True → False)) → ((p0 ∧ p7) ∧ (p6 ∨ p0))) ∨ (((p6 ∨ p7) ∧ (p7 ∨ p5)) → False))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    have assump_52 : ((p5 → p7) → (True ∨ p0)) := by
      intro assump_15
      apply Or.inl
      apply True.intro
    let assump_14 := assump_1 assump_52
    apply False.elim assump_14
  apply Or.inl
  intro assump_21
  apply And.intro
  apply And.intro
  have assump_53 : (False → False) := by
    intro assump_25
    apply False.elim assump_25
  let assump_24 := assump_21 assump_53
  have assump_54 : True := by
    apply True.intro
  let assump_28 := assump_24 assump_54
  apply False.elim assump_28
  have assump_55 : (False → False) := by
    intro assump_35
    apply False.elim assump_35
  let assump_34 := assump_21 assump_55
  have assump_56 : True := by
    apply True.intro
  let assump_38 := assump_34 assump_56
  apply False.elim assump_38
  have assump_57 : (False → False) := by
    intro assump_45
    apply False.elim assump_45
  let assump_44 := assump_21 assump_57
  have assump_58 : True := by
    apply True.intro
  let assump_48 := assump_44 assump_58
  apply False.elim assump_48


variable (p3 : Prop)
theorem file96_6976 : (((((p3 → p3) → False) → False) → False) → False) := by
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


variable (p4 p3 p5 p6 p1 p0 p7 : Prop)
theorem file96_7399 : (((((p0 ∧ p6) → (p0 ∨ p6)) ∧ ((p3 ∧ p3) ∨ (p0 → p5))) ∨ (((p4 → p7) ∨ (p1 ∧ p7)) → False)) → ((((p7 ∧ p5) ∧ (p6 ∨ True)) ∧ ((p5 → False) ∧ (False → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_6
        case inl assump_13 =>
          cases assump_4
          case intro assump_17 assump_18 =>
            cases assump_1
            case inl assump_23 =>
              cases assump_23
              case intro assump_25 assump_26 =>
                cases assump_26
                case inl assump_29 =>
                  cases assump_29
                  case intro assump_31 assump_32 =>
                    have assump_111 : p5 := by
                      exact assump_8
                    let assump_41 := assump_17 assump_111
                    apply False.elim assump_41
                case inr assump_30 =>
                  have assump_112 : p5 := by
                    exact assump_8
                  let assump_50 := assump_17 assump_112
                  apply False.elim assump_50
            case inr assump_24 =>
              have assump_113 : ((p4 → p7) ∨ (p1 ∧ p7)) := by
                apply Or.inl
                intro assump_57
                exact assump_7
              let assump_56 := assump_24 assump_113
              apply False.elim assump_56
        case inr assump_14 =>
          cases assump_4
          case intro assump_65 assump_66 =>
            cases assump_1
            case inl assump_71 =>
              cases assump_71
              case intro assump_73 assump_74 =>
                cases assump_74
                case inl assump_77 =>
                  cases assump_77
                  case intro assump_79 assump_80 =>
                    have assump_114 : p5 := by
                      exact assump_8
                    let assump_89 := assump_65 assump_114
                    apply False.elim assump_89
                case inr assump_78 =>
                  have assump_115 : p5 := by
                    exact assump_8
                  let assump_98 := assump_65 assump_115
                  apply False.elim assump_98
            case inr assump_72 =>
              have assump_116 : ((p4 → p7) ∨ (p1 ∧ p7)) := by
                apply Or.inl
                intro assump_105
                exact assump_7
              let assump_104 := assump_72 assump_116
              apply False.elim assump_104


variable (p2 p0 p6 p4 p3 p7 p1 : Prop)
theorem file96_10026 : (((((p3 ∨ False) ∧ (p7 ∧ p4)) ∨ ((False → False) ∨ (False → False))) → False) → ((((p6 → p3) ∨ (p0 → p2)) → ((p4 → p1) → False)) ∨ (((p2 → False) → False) → ((p6 ∧ p6) ∧ (True → p7))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    have assump_32 : (((p3 ∨ False) ∧ (p7 ∧ p4)) ∨ ((False → False) ∨ (False → False))) := by
      apply Or.inr
      apply Or.inl
      intro assump_15
      apply False.elim assump_15
    let assump_14 := assump_1 assump_32
    apply False.elim assump_14
  case inr assump_9 =>
    have assump_33 : (((p3 ∨ False) ∧ (p7 ∧ p4)) ∨ ((False → False) ∨ (False → False))) := by
      apply Or.inr
      apply Or.inl
      intro assump_26
      apply False.elim assump_26
    let assump_25 := assump_1 assump_33
    apply False.elim assump_25


variable (p5 p1 p3 : Prop)
theorem file96_10914 : (((((p3 → False) → False) ∧ ((p1 ∨ True) → False)) → (((False ∨ False) ∨ (p3 ∧ True)) → False)) ∨ ((((p5 ∧ p3) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      apply False.elim assump_5
    case inr assump_6 =>
      apply False.elim assump_6
  case inr assump_4 =>
    cases assump_4
    case intro assump_11 assump_12 =>
      cases assump_1
      case intro assump_17 assump_18 =>
        have assump_27 : (p1 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_23 := assump_18 assump_27
        apply False.elim assump_23


variable (p2 p1 p3 p6 p7 : Prop)
theorem file96_11652 : (((((p7 ∨ p3) → (p3 ∧ False)) → ((p6 → p1) ∧ (p2 → False))) ∧ (((True ∨ p2) → False) ∧ ((p7 → p3) ∨ (p3 ∧ False)))) → False) := by
  intro assump_47
  cases assump_47
  case intro assump_48 assump_49 =>
    cases assump_49
    case intro assump_52 assump_53 =>
      cases assump_53
      case inl assump_56 =>
        have assump_71 : (True ∨ p2) := by
          apply Or.inl
          apply True.intro
        let assump_61 := assump_52 assump_71
        apply False.elim assump_61
      case inr assump_57 =>
        cases assump_57
        case intro assump_65 assump_66 =>
          apply False.elim assump_66


variable (p0 p6 p2 p3 p1 p4 p7 : Prop)
theorem file96_12330 : (((((p1 → False) ∨ (p6 ∧ p7)) ∨ ((p3 → p3) ∧ (p3 ∧ True))) → (((False ∧ p2) ∧ (p4 ∨ p3)) → False)) ∨ ((((p6 ∧ True) → False) ∧ ((p0 → False) → (p7 ∨ p4))) ∨ (((p0 ∧ p0) → (p7 → False)) ∧ ((True → p6) → (True ∨ p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5


variable (p0 p7 p5 p6 p1 p2 p3 : Prop)
theorem file96_12804 : ((((((p3 ∧ False) ∧ (p6 → False)) → ((p6 ∧ p5) ∧ (p6 → False))) ∧ (((p0 → False) ∨ (p7 → False)) → ((p2 ∧ False) → (p1 → p5)))) → False) → False) := by
  intro assump_1
  have assump_47 : ((((p3 ∧ False) ∧ (p6 → False)) → ((p6 ∧ p5) ∧ (p6 → False))) ∧ (((p0 → False) ∨ (p7 → False)) → ((p2 ∧ False) → (p1 → p5)))) := by
    apply And.intro
    intro assump_5
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
    cases assump_5
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        apply False.elim assump_17
    intro assump_22
    cases assump_5
    case intro assump_25 assump_26 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        apply False.elim assump_28
    intro assump_33
    intro assump_34
    intro assump_35
    cases assump_34
    case intro assump_38 assump_39 =>
      apply False.elim assump_39
  let assump_4 := assump_1 assump_47
  apply False.elim assump_4


variable (p7 p2 p1 p0 p4 p5 p3 : Prop)
theorem file96_13958 : ((((((True ∧ p5) → False) ∨ ((p1 ∧ p7) → False)) ∧ (((p0 ∨ p1) → False) ∧ ((p4 → False) ∧ (True → False)))) ∧ ((((True ∧ p7) → (p2 ∨ True)) ∨ ((p3 → p0) → False)) → (((False → p2) ∨ (True ∨ p7)) → False))) → False) := by
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
            have assump_66 : (((True ∧ p7) → (p2 ∨ True)) ∨ ((p3 → p0) → False)) := by
              apply Or.inl
              intro assump_23
              cases assump_23
              case intro assump_24 assump_25 =>
                apply Or.inr
                apply True.intro
            let assump_22 := assump_3 assump_66
            have assump_67 : ((False → p2) ∨ (True ∨ p7)) := by
              apply Or.inl
              intro assump_31
              apply False.elim assump_31
            let assump_30 := assump_22 assump_67
            apply False.elim assump_30
      case inr assump_7 =>
        cases assump_5
        case intro assump_39 assump_40 =>
          cases assump_40
          case intro assump_43 assump_44 =>
            have assump_68 : (((True ∧ p7) → (p2 ∨ True)) ∨ ((p3 → p0) → False)) := by
              apply Or.inl
              intro assump_52
              cases assump_52
              case intro assump_53 assump_54 =>
                apply Or.inr
                apply True.intro
            let assump_51 := assump_3 assump_68
            have assump_69 : ((False → p2) ∨ (True ∨ p7)) := by
              apply Or.inl
              intro assump_60
              apply False.elim assump_60
            let assump_59 := assump_51 assump_69
            apply False.elim assump_59


variable (p4 p6 p1 p7 p3 p5 p2 p0 : Prop)
theorem file96_15877 : (((((False → False) ∨ (p2 → p1)) → False) → (((p7 ∧ p4) ∧ (p1 ∨ p3)) → ((p6 → False) ∧ (False → p0)))) ∨ ((((False ∧ p3) ∨ (True ∧ p5)) ∧ ((p0 ∧ p2) ∧ (True → p6))) → (((True ∨ p3) ∨ (True → False)) → ((p1 ∨ p3) ∧ (p6 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_7
      case inl assump_14 =>
        have assump_41 : ((False → False) ∨ (p2 → p1)) := by
          apply Or.inl
          intro assump_21
          apply False.elim assump_21
        let assump_20 := assump_1 assump_41
        apply False.elim assump_20
      case inr assump_15 =>
        have assump_42 : ((False → False) ∨ (p2 → p1)) := by
          apply Or.inl
          intro assump_32
          apply False.elim assump_32
        let assump_31 := assump_1 assump_42
        apply False.elim assump_31
  intro assump_38
  apply False.elim assump_38


variable (p0 p5 p4 p1 p6 p3 : Prop)
theorem file96_16940 : (((((True → p3) → (p5 → False)) → ((p4 → True) ∨ (True → False))) ∨ (((p1 ∧ p5) ∧ (p4 → p6)) → ((p4 ∨ p1) ∧ (p5 → False)))) ∨ ((((p3 → False) → False) → ((p3 → False) → False)) → (((False ∧ True) → (p6 ∧ p1)) ∨ ((p5 → True) ∨ (p0 → p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply True.intro


variable (p5 p0 p3 p7 p2 p6 : Prop)
theorem file96_17344 : ((((((p0 → p6) → False) ∨ ((p7 → p6) ∧ (p3 → p3))) → (((p2 ∧ p6) ∨ (p5 ∧ p6)) ∨ ((p3 ∧ True) ∨ (p2 → True)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p0 → p6) → False) ∨ ((p7 → p6) ∧ (p3 → p3))) → (((p2 ∧ p6) ∨ (p5 ∧ p6)) ∨ ((p3 ∧ True) ∨ (p2 → True)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inr
      apply Or.inr
      intro assump_10
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case intro assump_11 assump_12 =>
        apply Or.inr
        apply Or.inr
        intro assump_17
        apply True.intro
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p4 p6 p3 p7 p2 p5 p0 : Prop)
theorem file96_18079 : ((((((False ∧ p7) ∧ (p0 ∨ p3)) ∨ ((p6 → False) ∧ (p3 ∧ p2))) → False) ∧ ((((p5 ∧ p7) ∧ (p5 → False)) → ((p4 → False) ∨ (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_31 : (((p5 ∧ p7) ∧ (p5 → False)) → ((p4 → False) ∨ (False → False))) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_20
          have assump_32 : p5 := by
            exact assump_12
          let assump_24 := assump_11 assump_32
          apply False.elim assump_24
    let assump_8 := assump_3 assump_31
    apply False.elim assump_8


variable (p6 p5 p0 p3 p2 p4 p1 p7 : Prop)
theorem file96_18880 : (((((p3 → False) ∧ (p0 ∧ p3)) ∧ ((p5 → False) ∨ (True ∨ p1))) → False) ∨ ((((False → False) ∨ (p6 → True)) ∧ ((False ∧ False) → (p1 ∨ p4))) ∧ (((p5 → False) ∧ (p2 → False)) ∧ ((p0 → True) ∨ (p1 ∨ p7))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_3
        case inl assump_14 =>
          have assump_44 : p3 := by
            exact assump_9
          let assump_21 := assump_4 assump_44
          apply False.elim assump_21
        case inr assump_15 =>
          cases assump_15
          case inl assump_25 =>
            have assump_45 : p3 := by
              exact assump_9
            let assump_31 := assump_4 assump_45
            apply False.elim assump_31
          case inr assump_26 =>
            have assump_46 : p3 := by
              exact assump_9
            let assump_40 := assump_4 assump_46
            apply False.elim assump_40


variable (p0 p1 p7 p5 : Prop)
theorem file96_19968 : (((((False → False) ∧ (p7 ∨ p7)) ∨ ((p0 → p0) → (p0 → False))) → (((p7 ∧ False) ∧ (p5 → False)) → ((p1 → p1) ∧ (p5 → False)))) → ((((p5 → True) ∨ (False → False)) → ((False ∧ True) → False)) ∨ (((True → p5) → False) → ((False → False) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply False.elim assump_6


variable (p3 p7 p1 p5 p0 p6 p2 p4 : Prop)
theorem file96_20434 : (((((True ∧ p6) ∧ (p6 → False)) ∧ ((p4 ∧ p3) → False)) → (((p0 ∧ p2) → (True → p0)) ∨ ((p3 ∧ p7) ∧ (p0 ∨ p1)))) ∨ ((((True ∨ True) → False) → False) → (((p4 ∨ p2) → (p5 → False)) ∧ ((p3 → p1) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply Or.inl
        intro assump_16
        intro assump_17
        cases assump_16
        case intro assump_20 assump_21 =>
          exact assump_20


variable (p0 p3 p6 p5 p2 p7 p1 : Prop)
theorem file96_21065 : (((((p6 ∧ p5) → False) → ((p0 → False) ∧ (p1 ∧ p5))) → (((True → p3) → False) → ((p5 → False) → (False → p2)))) ∨ ((((False → True) ∨ (p3 ∨ p3)) → ((p5 → False) ∨ (p7 → p6))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply False.elim assump_4


variable (p1 p7 p2 p4 p3 p5 p6 p0 : Prop)
theorem file96_21433 : (((((p0 → p6) → (False → p3)) ∨ ((p7 → False) → False)) ∧ (((p4 ∨ p4) ∧ (p4 → False)) → ((p3 ∨ False) ∧ (p0 ∨ False)))) ∨ ((((p1 ∧ False) → (True ∧ p5)) ∧ ((p7 ∧ p6) → False)) → (((p3 → p4) → (p1 → False)) ∧ ((p3 → p6) ∨ (p2 ∨ p0))))) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_5
  intro assump_6
  apply False.elim assump_6
  intro assump_9
  apply And.intro
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case inl assump_12 =>
      have assump_50 : p4 := by
        exact assump_12
      let assump_18 := assump_11 assump_50
      apply False.elim assump_18
    case inr assump_13 =>
      have assump_51 : p4 := by
        exact assump_13
      let assump_26 := assump_11 assump_51
      apply False.elim assump_26
  cases assump_9
  case intro assump_30 assump_31 =>
    cases assump_30
    case inl assump_32 =>
      have assump_52 : p4 := by
        exact assump_32
      let assump_38 := assump_31 assump_52
      apply False.elim assump_38
    case inr assump_33 =>
      have assump_53 : p4 := by
        exact assump_33
      let assump_46 := assump_31 assump_53
      apply False.elim assump_46


variable (p0 p1 p7 p4 p5 : Prop)
theorem file96_22654 : (((((p0 → True) ∧ (p7 → p1)) ∧ ((p5 ∧ True) ∨ (p5 → False))) → (((True ∨ True) ∧ (p1 ∧ False)) → False)) ∨ ((((p5 ∨ p4) → False) → ((p4 → p5) → False)) → False)) := by
  apply Or.inl
  intro assump_6
  intro assump_7
  cases assump_7
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


variable (p5 p1 p2 p0 p6 p3 p7 p4 : Prop)
theorem file96_23251 : ((((((p2 ∧ False) ∧ (p4 ∨ p3)) ∧ ((p3 → p3) → False)) ∧ (((p4 ∧ p6) → (p6 → p0)) → False)) ∧ ((((p5 ∧ p7) → (p1 → False)) → False) ∨ (((p5 → p3) → (p1 ∧ p2)) ∨ ((True ∨ False) → (p5 → False))))) → False) := by
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


variable (p4 p2 p7 p6 p1 p3 p0 : Prop)
theorem file96_23877 : ((((((p2 → p0) ∧ (p3 ∧ p0)) ∨ ((p7 ∨ True) ∨ (True ∧ p0))) ∨ (((p6 → p2) ∨ (p0 ∧ False)) → False)) ∧ ((((p6 → False) → (False ∨ p1)) → ((p1 ∧ False) → (p1 → p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case intro assump_12 assump_13 =>
            have assump_119 : (((p6 → False) → (False ∨ p1)) → ((p1 ∧ False) → (p1 → p4))) := by
              intro assump_21
              intro assump_22
              intro assump_23
              cases assump_22
              case intro assump_26 assump_27 =>
                apply False.elim assump_27
            let assump_20 := assump_3 assump_119
            apply False.elim assump_20
      case inr assump_7 =>
        cases assump_7
        case inl assump_35 =>
          cases assump_35
          case inl assump_37 =>
            have assump_120 : (((p6 → False) → (False ∨ p1)) → ((p1 ∧ False) → (p1 → p4))) := by
              intro assump_44
              intro assump_45
              intro assump_46
              cases assump_45
              case intro assump_49 assump_50 =>
                apply False.elim assump_50
            let assump_43 := assump_3 assump_120
            apply False.elim assump_43
          case inr assump_38 =>
            have assump_121 : (((p6 → False) → (False ∨ p1)) → ((p1 ∧ False) → (p1 → p4))) := by
              intro assump_63
              intro assump_64
              intro assump_65
              cases assump_64
              case intro assump_68 assump_69 =>
                apply False.elim assump_69
            let assump_62 := assump_3 assump_121
            apply False.elim assump_62
        case inr assump_36 =>
          cases assump_36
          case intro assump_77 assump_78 =>
            have assump_122 : (((p6 → False) → (False ∨ p1)) → ((p1 ∧ False) → (p1 → p4))) := by
              intro assump_86
              intro assump_87
              intro assump_88
              cases assump_87
              case intro assump_91 assump_92 =>
                apply False.elim assump_92
            let assump_85 := assump_3 assump_122
            apply False.elim assump_85
    case inr assump_5 =>
      have assump_123 : (((p6 → False) → (False ∨ p1)) → ((p1 ∧ False) → (p1 → p4))) := by
        intro assump_105
        intro assump_106
        intro assump_107
        cases assump_106
        case intro assump_110 assump_111 =>
          apply False.elim assump_111
      let assump_104 := assump_3 assump_123
      apply False.elim assump_104


variable (p4 p0 p3 p1 p5 : Prop)
theorem file96_26644 : (((((True → False) ∧ (p5 → False)) ∧ ((p3 ∧ p4) ∨ (p0 ∨ p1))) → False) ∨ ((((p3 → True) → False) ∨ ((p3 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_7
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          have assump_47 : True := by
            apply True.intro
          let assump_25 := assump_8 assump_47
          apply False.elim assump_25
      case inr assump_15 =>
        cases assump_15
        case inl assump_29 =>
          have assump_48 : True := by
            apply True.intro
          let assump_35 := assump_8 assump_48
          apply False.elim assump_35
        case inr assump_30 =>
          have assump_49 : True := by
            apply True.intro
          let assump_43 := assump_8 assump_49
          apply False.elim assump_43


variable (p6 p0 p1 p2 p3 p5 : Prop)
theorem file96_27658 : (((((False ∨ p3) → False) ∧ ((True → p1) ∧ (p0 → False))) ∧ (((False ∨ True) ∧ (p5 ∧ p0)) → ((p6 ∧ p1) → False))) → ((((p1 ∨ True) → False) → ((p5 ∧ p1) → (p2 ∧ p2))) ∧ (((p5 ∧ p0) ∧ (p0 → p6)) → False))) := by
  intro assump_31
  apply And.intro
  intro assump_32
  intro assump_33
  apply And.intro
  cases assump_33
  case intro assump_34 assump_35 =>
    cases assump_31
    case intro assump_42 assump_43 =>
      cases assump_42
      case intro assump_44 assump_45 =>
        cases assump_45
        case intro assump_48 assump_49 =>
          have assump_127 : (p1 ∨ True) := by
            apply Or.inl
            exact assump_35
          let assump_61 := assump_32 assump_127
          apply False.elim assump_61
  cases assump_33
  case intro assump_65 assump_66 =>
    cases assump_31
    case intro assump_73 assump_74 =>
      cases assump_73
      case intro assump_75 assump_76 =>
        cases assump_76
        case intro assump_79 assump_80 =>
          have assump_128 : (p1 ∨ True) := by
            apply Or.inl
            exact assump_66
          let assump_92 := assump_32 assump_128
          apply False.elim assump_92
  intro assump_96
  cases assump_96
  case intro assump_97 assump_98 =>
    cases assump_97
    case intro assump_99 assump_100 =>
      cases assump_31
      case intro assump_107 assump_108 =>
        cases assump_107
        case intro assump_109 assump_110 =>
          cases assump_110
          case intro assump_113 assump_114 =>
            have assump_129 : p0 := by
              exact assump_100
            let assump_123 := assump_114 assump_129
            apply False.elim assump_123


variable (p0 p3 p6 p4 p5 : Prop)
theorem file96_29363 : ((((((p6 → False) ∨ (p5 → p4)) → ((True → False) → (False → False))) → False) ∨ ((((True → False) ∧ (p0 ∧ p3)) → ((False → p0) → (False ∧ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_59 : (((p6 → False) ∨ (p5 → p4)) → ((True → False) → (False → False))) := by
      intro assump_7
      intro assump_8
      intro assump_9
      apply False.elim assump_9
    let assump_6 := assump_2 assump_59
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_60 : (((True → False) ∧ (p0 ∧ p3)) → ((False → p0) → (False ∧ p6))) := by
      intro assump_18
      intro assump_19
      apply And.intro
      cases assump_18
      case intro assump_22 assump_23 =>
        cases assump_23
        case intro assump_26 assump_27 =>
          have assump_61 : True := by
            apply True.intro
          let assump_34 := assump_22 assump_61
          apply False.elim assump_34
      cases assump_18
      case intro assump_40 assump_41 =>
        cases assump_41
        case intro assump_44 assump_45 =>
          have assump_62 : True := by
            apply True.intro
          let assump_52 := assump_40 assump_62
          apply False.elim assump_52
    let assump_17 := assump_3 assump_60
    apply False.elim assump_17


variable (p4 p5 p2 p1 p0 p3 p7 : Prop)
theorem file96_30717 : (((((p1 ∧ False) ∧ (p5 → False)) ∨ ((p1 → p5) ∧ (p0 → False))) → (((p0 → False) → (True ∨ p4)) ∨ ((p5 ∨ p1) ∨ (p4 → False)))) ∧ ((((p1 ∧ p3) ∧ (False ∨ True)) → ((p0 ∨ p7) ∨ (False ∨ p3))) ∧ (((False ∨ True) → False) → ((p4 ∨ p2) ∨ (p1 ∨ False))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_7
  case inr assump_3 =>
    cases assump_3
    case intro assump_12 assump_13 =>
      apply Or.inl
      intro assump_18
      apply Or.inl
      apply True.intro
  apply And.intro
  intro assump_21
  cases assump_21
  case intro assump_22 assump_23 =>
    cases assump_22
    case intro assump_24 assump_25 =>
      cases assump_23
      case inl assump_30 =>
        apply False.elim assump_30
      case inr assump_31 =>
        apply Or.inr
        apply Or.inr
        exact assump_25
  intro assump_36
  have assump_43 : (False ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_39 := assump_36 assump_43
  apply False.elim assump_39


variable (p0 p3 p1 p4 p2 p6 p5 : Prop)
theorem file96_31912 : ((((((p4 ∨ p4) ∨ (p1 ∨ p6)) → False) ∧ (((p6 ∨ p1) ∧ (p0 → False)) ∧ ((p0 ∨ p2) → False))) ∧ ((((p0 ∨ p2) ∧ (p3 → False)) → False) ∨ (((p2 → False) ∧ (p5 ∨ p3)) ∨ ((p4 → p4) ∨ (True → False))))) → False) := by
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
          case inl assump_12 =>
            cases assump_3
            case inl assump_20 =>
              have assump_146 : ((p4 ∨ p4) ∨ (p1 ∨ p6)) := by
                apply Or.inr
                apply Or.inr
                exact assump_12
              let assump_28 := assump_4 assump_146
              apply False.elim assump_28
            case inr assump_21 =>
              cases assump_21
              case inl assump_32 =>
                cases assump_32
                case intro assump_34 assump_35 =>
                  cases assump_35
                  case inl assump_38 =>
                    have assump_147 : ((p4 ∨ p4) ∨ (p1 ∨ p6)) := by
                      apply Or.inr
                      apply Or.inr
                      exact assump_12
                    let assump_47 := assump_4 assump_147
                    apply False.elim assump_47
                  case inr assump_39 =>
                    have assump_148 : ((p4 ∨ p4) ∨ (p1 ∨ p6)) := by
                      apply Or.inr
                      apply Or.inr
                      exact assump_12
                    let assump_58 := assump_4 assump_148
                    apply False.elim assump_58
              case inr assump_33 =>
                cases assump_33
                case inl assump_62 =>
                  have assump_149 : ((p4 ∨ p4) ∨ (p1 ∨ p6)) := by
                    apply Or.inr
                    apply Or.inr
                    exact assump_12
                  let assump_70 := assump_4 assump_149
                  apply False.elim assump_70
                case inr assump_63 =>
                  have assump_150 : True := by
                    apply True.intro
                  let assump_76 := assump_63 assump_150
                  apply False.elim assump_76
          case inr assump_13 =>
            cases assump_3
            case inl assump_86 =>
              have assump_151 : ((p4 ∨ p4) ∨ (p1 ∨ p6)) := by
                apply Or.inr
                apply Or.inl
                exact assump_13
              let assump_94 := assump_4 assump_151
              apply False.elim assump_94
            case inr assump_87 =>
              cases assump_87
              case inl assump_98 =>
                cases assump_98
                case intro assump_100 assump_101 =>
                  cases assump_101
                  case inl assump_104 =>
                    have assump_152 : ((p4 ∨ p4) ∨ (p1 ∨ p6)) := by
                      apply Or.inr
                      apply Or.inl
                      exact assump_13
                    let assump_113 := assump_4 assump_152
                    apply False.elim assump_113
                  case inr assump_105 =>
                    have assump_153 : ((p4 ∨ p4) ∨ (p1 ∨ p6)) := by
                      apply Or.inr
                      apply Or.inl
                      exact assump_13
                    let assump_124 := assump_4 assump_153
                    apply False.elim assump_124
              case inr assump_99 =>
                cases assump_99
                case inl assump_128 =>
                  have assump_154 : ((p4 ∨ p4) ∨ (p1 ∨ p6)) := by
                    apply Or.inr
                    apply Or.inl
                    exact assump_13
                  let assump_136 := assump_4 assump_154
                  apply False.elim assump_136
                case inr assump_129 =>
                  have assump_155 : True := by
                    apply True.intro
                  let assump_142 := assump_129 assump_155
                  apply False.elim assump_142


variable (p3 p5 p2 p0 p6 : Prop)
theorem file96_36048 : ((((((p5 ∧ True) ∨ (True ∧ p3)) ∨ ((p3 → False) ∧ (p0 → False))) ∨ (((p6 ∨ True) → False) → ((False → False) → False))) ∧ ((((p2 ∧ False) ∧ (p5 → False)) → False) → False)) → False) := by
  intro assump_68
  cases assump_68
  case intro assump_69 assump_70 =>
    cases assump_69
    case inl assump_71 =>
      cases assump_71
      case inl assump_73 =>
        cases assump_73
        case inl assump_75 =>
          cases assump_75
          case intro assump_77 assump_78 =>
            have assump_157 : (((p2 ∧ False) ∧ (p5 → False)) → False) := by
              intro assump_86
              cases assump_86
              case intro assump_87 assump_88 =>
                cases assump_87
                case intro assump_89 assump_90 =>
                  apply False.elim assump_90
            let assump_85 := assump_70 assump_157
            apply False.elim assump_85
        case inr assump_76 =>
          cases assump_76
          case intro assump_98 assump_99 =>
            have assump_158 : (((p2 ∧ False) ∧ (p5 → False)) → False) := by
              intro assump_107
              cases assump_107
              case intro assump_108 assump_109 =>
                cases assump_108
                case intro assump_110 assump_111 =>
                  apply False.elim assump_111
            let assump_106 := assump_70 assump_158
            apply False.elim assump_106
      case inr assump_74 =>
        cases assump_74
        case intro assump_119 assump_120 =>
          have assump_159 : (((p2 ∧ False) ∧ (p5 → False)) → False) := by
            intro assump_128
            cases assump_128
            case intro assump_129 assump_130 =>
              cases assump_129
              case intro assump_131 assump_132 =>
                apply False.elim assump_132
          let assump_127 := assump_70 assump_159
          apply False.elim assump_127
    case inr assump_72 =>
      have assump_160 : (((p2 ∧ False) ∧ (p5 → False)) → False) := by
        intro assump_145
        cases assump_145
        case intro assump_146 assump_147 =>
          cases assump_146
          case intro assump_148 assump_149 =>
            apply False.elim assump_149
      let assump_144 := assump_70 assump_160
      apply False.elim assump_144


variable (p2 p3 p5 p4 p0 : Prop)
theorem file96_38365 : (((((False → False) ∨ (p0 → False)) → ((False → False) → (p0 → False))) → (((p2 ∧ False) ∧ (p4 → p4)) → ((False ∧ p5) → False))) ∨ ((((False → p5) ∧ (p2 ∨ True)) ∧ ((p3 ∨ p3) → False)) → (((True ∧ True) ∨ (p4 ∧ True)) → ((False → False) → False)))) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p2 p3 p5 p6 p0 p4 p7 : Prop)
theorem file96_38830 : ((((((p2 → False) → (p7 ∨ p4)) → ((True → p4) → (False ∨ p6))) → (((p3 ∨ p2) ∧ (p3 → p3)) ∨ ((p7 ∨ p2) ∨ (p0 ∧ p3)))) ∧ ((((p6 → p3) → (p7 → p4)) → ((p6 ∧ p3) → (p5 → False))) ∧ (((p6 ∨ True) ∧ (True ∨ False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_16 : ((p6 ∨ True) ∧ (True ∨ False)) := by
        apply And.intro
        apply Or.inr
        apply True.intro
        apply Or.inl
        apply True.intro
      let assump_12 := assump_7 assump_16
      apply False.elim assump_12


variable (p6 p7 p5 p4 p3 p0 p1 : Prop)
theorem file96_39503 : ((((((p4 ∧ p0) → (True ∧ True)) → ((p1 → False) ∨ (p6 ∨ p0))) ∨ (((p4 → p0) ∨ (p7 ∨ p6)) → False)) ∧ ((((p6 → p5) → (p7 → False)) → ((p3 ∨ p0) ∨ (True ∨ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_28 : (((p6 → p5) → (p7 → False)) → ((p3 ∨ p0) ∨ (True ∨ p0))) := by
        intro assump_11
        apply Or.inr
        apply Or.inl
        apply True.intro
      let assump_10 := assump_3 assump_28
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_29 : (((p6 → p5) → (p7 → False)) → ((p3 ∨ p0) ∨ (True ∨ p0))) := by
        intro assump_22
        apply Or.inr
        apply Or.inl
        apply True.intro
      let assump_21 := assump_3 assump_29
      apply False.elim assump_21


variable (p0 p2 p5 p6 p3 p1 p7 : Prop)
theorem file96_40391 : ((((((p5 ∧ False) ∧ (p7 ∧ p0)) ∨ ((True → False) ∨ (p0 ∨ p6))) ∧ (((False → False) ∨ (p7 → False)) → False)) ∧ ((((p3 → p3) → (True ∧ p5)) ∨ ((p6 → False) ∧ (p1 → p0))) ∨ (((False → False) ∧ (True ∧ p1)) → ((p3 ∨ p2) ∧ (p5 → True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            apply False.elim assump_11
      case inr assump_7 =>
        cases assump_7
        case inl assump_16 =>
          cases assump_3
          case inl assump_22 =>
            cases assump_22
            case inl assump_24 =>
              have assump_172 : ((False → False) ∨ (p7 → False)) := by
                apply Or.inl
                intro assump_36
                apply False.elim assump_36
              let assump_35 := assump_5 assump_172
              apply False.elim assump_35
            case inr assump_25 =>
              cases assump_25
              case intro assump_42 assump_43 =>
                have assump_173 : ((False → False) ∨ (p7 → False)) := by
                  apply Or.inl
                  intro assump_51
                  apply False.elim assump_51
                let assump_50 := assump_5 assump_173
                apply False.elim assump_50
          case inr assump_23 =>
            have assump_174 : ((False → False) ∨ (p7 → False)) := by
              apply Or.inl
              intro assump_64
              apply False.elim assump_64
            let assump_63 := assump_5 assump_174
            apply False.elim assump_63
        case inr assump_17 =>
          cases assump_17
          case inl assump_70 =>
            cases assump_3
            case inl assump_76 =>
              cases assump_76
              case inl assump_78 =>
                have assump_175 : ((False → False) ∨ (p7 → False)) := by
                  apply Or.inl
                  intro assump_90
                  apply False.elim assump_90
                let assump_89 := assump_5 assump_175
                apply False.elim assump_89
              case inr assump_79 =>
                cases assump_79
                case intro assump_96 assump_97 =>
                  have assump_176 : ((False → False) ∨ (p7 → False)) := by
                    apply Or.inl
                    intro assump_105
                    apply False.elim assump_105
                  let assump_104 := assump_5 assump_176
                  apply False.elim assump_104
            case inr assump_77 =>
              have assump_177 : ((False → False) ∨ (p7 → False)) := by
                apply Or.inl
                intro assump_118
                apply False.elim assump_118
              let assump_117 := assump_5 assump_177
              apply False.elim assump_117
          case inr assump_71 =>
            cases assump_3
            case inl assump_128 =>
              cases assump_128
              case inl assump_130 =>
                have assump_178 : ((False → False) ∨ (p7 → False)) := by
                  apply Or.inl
                  intro assump_142
                  apply False.elim assump_142
                let assump_141 := assump_5 assump_178
                apply False.elim assump_141
              case inr assump_131 =>
                cases assump_131
                case intro assump_148 assump_149 =>
                  have assump_179 : p6 := by
                    exact assump_71
                  let assump_155 := assump_148 assump_179
                  apply False.elim assump_155
            case inr assump_129 =>
              have assump_180 : ((False → False) ∨ (p7 → False)) := by
                apply Or.inl
                intro assump_166
                apply False.elim assump_166
              let assump_165 := assump_5 assump_180
              apply False.elim assump_165


variable (p0 p4 p1 p6 p7 p5 p3 : Prop)
theorem file96_44460 : ((((((p5 → p0) ∧ (p5 → False)) ∧ ((True → p5) ∧ (True ∨ p6))) → (((p0 ∨ p3) → (p4 ∨ p4)) ∨ ((p1 → False) ∨ (p1 → False)))) ∧ ((((False → p0) → False) → ((p0 ∧ p4) ∨ (p7 ∨ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((False → p0) → False) → ((p0 ∧ p4) ∨ (p7 ∨ p3))) := by
      intro assump_9
      have assump_23 : (False → p0) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_9 assump_23
      apply False.elim assump_12
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p2 p0 p7 p6 p5 p3 p1 : Prop)
theorem file96_45137 : (((((False ∧ p7) → False) → False) → (((False → False) → False) ∧ ((p0 → p5) → False))) ∨ ((((False → False) ∨ (p5 ∨ p6)) ∨ ((False → p7) → (p6 → p2))) ∨ (((p1 → False) ∨ (p2 → p7)) ∨ ((False ∨ p3) ∧ (p5 ∧ p5))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_30 : ((False ∧ p7) → False) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_7 := assump_1 assump_30
  apply False.elim assump_7
  intro assump_16
  have assump_31 : ((False ∧ p7) → False) := by
    intro assump_22
    cases assump_22
    case intro assump_23 assump_24 =>
      apply False.elim assump_23
  let assump_21 := assump_1 assump_31
  apply False.elim assump_21


variable (p3 p1 p7 : Prop)
theorem file96_45939 : ((((((p1 ∧ p3) ∧ (p7 → p1)) ∧ ((False → False) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p1 ∧ p3) ∧ (p7 → p1)) ∧ ((False → False) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_31 : (False → False) := by
            intro assump_21
            apply False.elim assump_21
          let assump_20 := assump_7 assump_31
          apply False.elim assump_20
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p7 p5 p4 p0 p1 p2 p3 : Prop)
theorem file96_46660 : (((((p5 ∧ p4) ∨ (p2 ∨ p5)) → ((p4 ∧ False) → (p3 ∨ False))) → False) → ((((False → p1) ∨ (p0 ∨ False)) → False) → (((p3 ∧ p2) → False) → ((p0 ∨ p1) ∨ (True ∨ p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p5 p7 p1 p4 p3 p6 p2 p0 : Prop)
theorem file96_46998 : (((((p6 ∨ True) ∧ (p7 → p4)) ∧ ((p5 ∧ False) → (p6 → p1))) → (((True → p7) ∨ (True → False)) → ((p5 ∨ p3) → False))) → ((((p2 ∨ p1) → (p2 ∨ True)) ∨ ((p0 → p6) ∨ (p1 ∧ p4))) ∨ (((p4 → p3) ∨ (p3 → False)) → ((p1 ∧ False) ∧ (p4 → False))))) := by
  intro assump_9
  apply Or.inl
  apply Or.inl
  intro assump_12
  cases assump_12
  case inl assump_13 =>
    apply Or.inl
    exact assump_13
  case inr assump_14 =>
    apply Or.inr
    apply True.intro


variable (p1 p0 p3 : Prop)
theorem file96_47500 : ((((((p3 ∨ True) → False) ∧ ((p1 → False) ∨ (p0 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p3 ∨ True) → False) ∧ ((p1 → False) ∨ (p0 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_30 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_15 := assump_6 assump_30
        apply False.elim assump_15
      case inr assump_11 =>
        have assump_31 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_22 := assump_6 assump_31
        apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p3 p0 p4 p5 p7 p1 p6 : Prop)
theorem file96_48323 : (((((p1 ∧ p3) ∧ (p0 → False)) → ((p5 ∨ p6) → False)) → False) → ((((p0 → False) → (p7 ∧ True)) → False) → (((p0 → False) ∨ (p6 → p4)) ∨ ((p6 ∨ p0) ∨ (False → False))))) := by
  intro assump_24
  intro assump_25
  apply Or.inl
  apply Or.inl
  intro assump_30
  have assump_74 : (((p1 ∧ p3) ∧ (p0 → False)) → ((p5 ∨ p6) → False)) := by
    intro assump_35
    intro assump_36
    cases assump_36
    case inl assump_37 =>
      cases assump_35
      case intro assump_41 assump_42 =>
        cases assump_41
        case intro assump_43 assump_44 =>
          have assump_75 : p0 := by
            exact assump_30
          let assump_51 := assump_42 assump_75
          apply False.elim assump_51
    case inr assump_38 =>
      cases assump_35
      case intro assump_57 assump_58 =>
        cases assump_57
        case intro assump_59 assump_60 =>
          have assump_76 : p0 := by
            exact assump_30
          let assump_67 := assump_58 assump_76
          apply False.elim assump_67
  let assump_34 := assump_24 assump_74
  apply False.elim assump_34


variable (p6 p4 p0 p7 p3 p1 p5 p2 : Prop)
theorem file96_49456 : ((((((False ∧ p0) → False) → ((False → False) ∨ (p3 ∧ p6))) → (((p5 → p0) ∨ (False → False)) ∧ ((p0 → False) ∧ (p7 → p4)))) ∧ ((((p3 ∨ p3) ∨ (p2 ∨ True)) → False) ∧ (((p6 ∧ True) → (p1 → p2)) ∨ ((p2 → True) ∧ (True → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_29 : ((p3 ∨ p3) ∨ (p2 ∨ True)) := by
          apply Or.inr
          apply Or.inr
          apply True.intro
        let assump_15 := assump_6 assump_29
        apply False.elim assump_15
      case inr assump_11 =>
        cases assump_11
        case intro assump_19 assump_20 =>
          have assump_30 : True := by
            apply True.intro
          let assump_25 := assump_20 assump_30
          apply False.elim assump_25


variable (p2 p5 p4 : Prop)
theorem file96_50376 : (((((p4 ∧ True) → False) → ((p4 → p4) ∨ (p2 → True))) → False) → ((((False → p4) → False) ∨ ((p5 → False) → (p4 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_33 : (((p4 ∧ True) → False) → ((p4 → p4) ∨ (p2 → True))) := by
      intro assump_10
      apply Or.inl
      intro assump_13
      exact assump_13
    let assump_9 := assump_1 assump_33
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_34 : (((p4 ∧ True) → False) → ((p4 → p4) ∨ (p2 → True))) := by
      intro assump_24
      apply Or.inl
      intro assump_27
      exact assump_27
    let assump_23 := assump_1 assump_34
    apply False.elim assump_23


variable (p0 p2 p6 p4 p3 p1 p7 : Prop)
theorem file96_51143 : ((((((p7 → False) ∧ (p3 ∧ p1)) ∧ ((p7 ∨ p0) ∨ (p4 ∧ p3))) ∧ (((p1 → False) → (False → False)) → False)) ∧ ((((p2 ∧ False) ∧ (p7 → False)) ∨ ((p6 ∧ False) ∧ (p3 ∨ p1))) → (((p2 ∧ True) → False) ∧ ((p7 → p7) → (p2 → p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case intro assump_12 assump_13 =>
            cases assump_7
            case inl assump_18 =>
              cases assump_18
              case inl assump_20 =>
                have assump_71 : ((p1 → False) → (False → False)) := by
                  intro assump_30
                  intro assump_31
                  apply False.elim assump_31
                let assump_29 := assump_5 assump_71
                apply False.elim assump_29
              case inr assump_21 =>
                have assump_72 : ((p1 → False) → (False → False)) := by
                  intro assump_45
                  intro assump_46
                  apply False.elim assump_46
                let assump_44 := assump_5 assump_72
                apply False.elim assump_44
            case inr assump_19 =>
              cases assump_19
              case intro assump_52 assump_53 =>
                have assump_73 : ((p1 → False) → (False → False)) := by
                  intro assump_64
                  intro assump_65
                  apply False.elim assump_65
                let assump_63 := assump_5 assump_73
                apply False.elim assump_63


variable (p1 : Prop)
theorem file96_52854 : (((((p1 ∨ True) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : (((p1 ∨ True) → False) → False) := by
    intro assump_5
    have assump_16 : (p1 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p5 p6 p7 : Prop)
theorem file96_53274 : ((((((p6 ∨ p5) ∧ (p5 → p4)) ∧ ((False ∧ p5) ∧ (p4 → p7))) → False) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p6 ∨ p5) ∧ (p5 → p4)) ∧ ((False ∧ p5) ∧ (p4 → p7))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_7
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              apply False.elim assump_18
        case inr assump_11 =>
          cases assump_7
          case intro assump_26 assump_27 =>
            cases assump_26
            case intro assump_28 assump_29 =>
              apply False.elim assump_28
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p1 p6 p0 p7 p4 p2 p5 p3 : Prop)
theorem file96_54187 : ((((((p0 → True) → (False → p2)) → False) ∧ (((False ∧ False) → (True ∨ p7)) → False)) ∧ ((((p7 → True) ∨ (p5 ∧ False)) ∨ ((p4 → False) ∨ (p3 → p0))) ∨ (((p1 → p1) → (p3 → p6)) ∨ ((p0 → False) ∧ (p1 ∨ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            have assump_99 : ((False ∧ False) → (True ∨ p7)) := by
              intro assump_20
              cases assump_20
              case intro assump_21 assump_22 =>
                apply False.elim assump_21
            let assump_19 := assump_5 assump_99
            apply False.elim assump_19
          case inr assump_15 =>
            cases assump_15
            case intro assump_28 assump_29 =>
              apply False.elim assump_29
        case inr assump_13 =>
          cases assump_13
          case inl assump_34 =>
            have assump_100 : ((False ∧ False) → (True ∨ p7)) := by
              intro assump_40
              cases assump_40
              case intro assump_41 assump_42 =>
                apply False.elim assump_41
            let assump_39 := assump_5 assump_100
            apply False.elim assump_39
          case inr assump_35 =>
            have assump_101 : ((False ∧ False) → (True ∨ p7)) := by
              intro assump_52
              cases assump_52
              case intro assump_53 assump_54 =>
                apply False.elim assump_53
            let assump_51 := assump_5 assump_101
            apply False.elim assump_51
      case inr assump_11 =>
        cases assump_11
        case inl assump_60 =>
          have assump_102 : ((False ∧ False) → (True ∨ p7)) := by
            intro assump_70
            cases assump_70
            case intro assump_71 assump_72 =>
              apply False.elim assump_71
          let assump_69 := assump_5 assump_102
          apply False.elim assump_69
        case inr assump_61 =>
          cases assump_61
          case intro assump_78 assump_79 =>
            cases assump_79
            case inl assump_82 =>
              have assump_103 : ((False ∧ False) → (True ∨ p7)) := by
                intro assump_89
                cases assump_89
                case intro assump_90 assump_91 =>
                  apply False.elim assump_90
              let assump_88 := assump_5 assump_103
              apply False.elim assump_88
            case inr assump_83 =>
              apply False.elim assump_83


variable (p3 p0 p4 p1 p7 p2 : Prop)
theorem file96_56877 : ((((((p7 → p7) → False) → False) → False) ∧ ((((p0 ∧ False) ∨ (p7 ∧ p1)) ∧ ((p1 ∧ False) → (p2 ∧ p7))) → (((p0 → False) ∧ (p4 ∨ p3)) → False))) → False) := by
  intro assump_36
  cases assump_36
  case intro assump_37 assump_38 =>
    have assump_58 : (((p7 → p7) → False) → False) := by
      intro assump_45
      have assump_59 : (p7 → p7) := by
        intro assump_49
        exact assump_49
      let assump_48 := assump_45 assump_59
      apply False.elim assump_48
    let assump_44 := assump_37 assump_58
    apply False.elim assump_44


variable (p2 : Prop)
theorem file96_57467 : (((((False → p2) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : (((False → p2) → False) → False) := by
    intro assump_5
    have assump_19 : (False → p2) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p1 p2 p4 p5 p0 p6 p3 : Prop)
theorem file96_57913 : ((((((p0 ∨ p5) ∨ (p4 ∨ True)) ∨ ((p5 ∨ p0) → False)) ∨ (((False → False) ∨ (p4 ∨ p3)) → False)) ∧ ((((p2 → False) → (p6 → p3)) ∧ ((p3 → p1) → (p1 → False))) ∧ (((False → False) ∨ (p7 ∧ p7)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_3
            case intro assump_14 assump_15 =>
              cases assump_14
              case intro assump_16 assump_17 =>
                have assump_128 : ((False → False) ∨ (p7 ∧ p7)) := by
                  apply Or.inl
                  intro assump_25
                  apply False.elim assump_25
                let assump_24 := assump_15 assump_128
                apply False.elim assump_24
          case inr assump_11 =>
            cases assump_3
            case intro assump_33 assump_34 =>
              cases assump_33
              case intro assump_35 assump_36 =>
                have assump_129 : ((False → False) ∨ (p7 ∧ p7)) := by
                  apply Or.inl
                  intro assump_44
                  apply False.elim assump_44
                let assump_43 := assump_34 assump_129
                apply False.elim assump_43
        case inr assump_9 =>
          cases assump_9
          case inl assump_50 =>
            cases assump_3
            case intro assump_54 assump_55 =>
              cases assump_54
              case intro assump_56 assump_57 =>
                have assump_130 : ((False → False) ∨ (p7 ∧ p7)) := by
                  apply Or.inl
                  intro assump_65
                  apply False.elim assump_65
                let assump_64 := assump_55 assump_130
                apply False.elim assump_64
          case inr assump_51 =>
            cases assump_3
            case intro assump_73 assump_74 =>
              cases assump_73
              case intro assump_75 assump_76 =>
                have assump_131 : ((False → False) ∨ (p7 ∧ p7)) := by
                  apply Or.inl
                  intro assump_84
                  apply False.elim assump_84
                let assump_83 := assump_74 assump_131
                apply False.elim assump_83
      case inr assump_7 =>
        cases assump_3
        case intro assump_92 assump_93 =>
          cases assump_92
          case intro assump_94 assump_95 =>
            have assump_132 : ((False → False) ∨ (p7 ∧ p7)) := by
              apply Or.inl
              intro assump_103
              apply False.elim assump_103
            let assump_102 := assump_93 assump_132
            apply False.elim assump_102
    case inr assump_5 =>
      cases assump_3
      case intro assump_111 assump_112 =>
        cases assump_111
        case intro assump_113 assump_114 =>
          have assump_133 : ((False → False) ∨ (p7 ∧ p7)) := by
            apply Or.inl
            intro assump_122
            apply False.elim assump_122
          let assump_121 := assump_112 assump_133
          apply False.elim assump_121


variable (p2 p6 p1 p0 : Prop)
theorem file96_61136 : ((((((False → p1) ∨ (p2 ∨ False)) ∨ ((True → p1) ∧ (p0 → True))) ∧ (((p6 ∧ True) → (p2 → True)) ∨ ((True → False) → False))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False → p1) ∨ (p2 ∨ False)) ∨ ((True → p1) ∧ (p0 → True))) ∧ (((p6 ∧ True) → (p2 → True)) ∨ ((True → False) → False))) := by
    apply And.intro
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    apply True.intro
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p5 p0 p7 p6 p2 p1 p4 p3 : Prop)
theorem file96_61760 : (((((p4 ∧ p5) ∨ (p4 → False)) ∧ ((p0 ∧ p6) ∧ (p7 → True))) ∧ (((True ∨ p1) → False) ∧ ((p1 ∧ p0) ∨ (p0 → p6)))) → ((((p0 ∧ p4) ∨ (p3 ∨ p0)) ∧ ((True → False) ∧ (p3 ∧ p7))) ∨ (((p0 → False) → (p5 ∧ True)) ∧ ((p7 ∨ False) ∧ (p2 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_5
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_3
              case intro assump_24 assump_25 =>
                cases assump_25
                case inl assump_28 =>
                  cases assump_28
                  case intro assump_30 assump_31 =>
                    have assump_144 : (True ∨ p1) := by
                      apply Or.inl
                      apply True.intro
                    let assump_50 := assump_24 assump_144
                    apply False.elim assump_50
                case inr assump_29 =>
                  have assump_145 : (True ∨ p1) := by
                    apply Or.inl
                    apply True.intro
                  let assump_70 := assump_24 assump_145
                  apply False.elim assump_70
      case inr assump_7 =>
        cases assump_5
        case intro assump_76 assump_77 =>
          cases assump_76
          case intro assump_78 assump_79 =>
            cases assump_3
            case intro assump_86 assump_87 =>
              cases assump_87
              case inl assump_90 =>
                cases assump_90
                case intro assump_92 assump_93 =>
                  have assump_146 : (True ∨ p1) := by
                    apply Or.inl
                    apply True.intro
                  let assump_116 := assump_86 assump_146
                  apply False.elim assump_116
              case inr assump_91 =>
                have assump_147 : (True ∨ p1) := by
                  apply Or.inl
                  apply True.intro
                let assump_140 := assump_86 assump_147
                apply False.elim assump_140


variable (p0 p5 p4 p3 p1 p2 p7 p6 : Prop)
theorem file96_64042 : (((((p3 ∨ p6) → (p0 ∨ p7)) → ((p0 → False) ∧ (p1 → p4))) ∨ (((True → False) → False) ∨ ((p4 → p2) ∧ (p7 ∧ p1)))) → ((((True ∧ p3) → (p2 → False)) → ((p3 → p4) ∨ (p4 ∧ p2))) → (((p7 → p5) ∧ (p6 → False)) → ((p4 ∧ False) → (False ∨ p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p6 p0 p2 p7 p1 p5 p4 : Prop)
theorem file96_64498 : ((((((p1 ∨ p7) ∨ (p6 → True)) ∨ ((p7 → p4) → (p7 → p6))) → False) ∧ ((((p6 ∨ p2) → (p1 → True)) ∨ ((p5 → p4) ∧ (p7 ∨ p0))) → False)) → False) := by
  intro assump_48
  cases assump_48
  case intro assump_49 assump_50 =>
    have assump_61 : (((p6 ∨ p2) → (p1 → True)) ∨ ((p5 → p4) ∧ (p7 ∨ p0))) := by
      apply Or.inl
      intro assump_56
      intro assump_57
      apply True.intro
    let assump_55 := assump_50 assump_61
    apply False.elim assump_55


variable (p1 p3 p5 p7 p4 : Prop)
theorem file96_65014 : (((((p3 → p5) → False) ∧ ((p5 ∨ False) ∧ (p7 → p7))) → (((p1 ∨ False) → False) ∧ ((p7 → p4) ∧ (p4 ∧ p1)))) ∨ ((((p7 → False) → (p1 → False)) → False) ∧ (((p4 → p5) ∨ (p7 → False)) → False))) := by
  apply Or.inl
  intro assump_17
  apply And.intro
  intro assump_18
  cases assump_18
  case inl assump_19 =>
    cases assump_17
    case intro assump_23 assump_24 =>
      cases assump_24
      case intro assump_27 assump_28 =>
        cases assump_27
        case inl assump_29 =>
          have assump_121 : (p3 → p5) := by
            intro assump_38
            exact assump_29
          let assump_37 := assump_23 assump_121
          apply False.elim assump_37
        case inr assump_30 =>
          apply False.elim assump_30
  case inr assump_20 =>
    apply False.elim assump_20
  apply And.intro
  intro assump_48
  cases assump_17
  case intro assump_51 assump_52 =>
    cases assump_52
    case intro assump_55 assump_56 =>
      cases assump_55
      case inl assump_57 =>
        have assump_122 : (p3 → p5) := by
          intro assump_67
          exact assump_57
        let assump_66 := assump_51 assump_122
        apply False.elim assump_66
      case inr assump_58 =>
        apply False.elim assump_58
  apply And.intro
  cases assump_17
  case intro assump_75 assump_76 =>
    cases assump_76
    case intro assump_79 assump_80 =>
      cases assump_79
      case inl assump_81 =>
        have assump_123 : (p3 → p5) := by
          intro assump_90
          exact assump_81
        let assump_89 := assump_75 assump_123
        apply False.elim assump_89
      case inr assump_82 =>
        apply False.elim assump_82
  cases assump_17
  case intro assump_98 assump_99 =>
    cases assump_99
    case intro assump_102 assump_103 =>
      cases assump_102
      case inl assump_104 =>
        have assump_124 : (p3 → p5) := by
          intro assump_113
          exact assump_104
        let assump_112 := assump_98 assump_124
        apply False.elim assump_112
      case inr assump_105 =>
        apply False.elim assump_105


variable (p5 p0 p6 p1 p4 p7 : Prop)
theorem file96_67127 : ((((((p4 ∧ p5) → (p1 → p7)) ∨ ((p6 → False) → (p0 ∨ p7))) ∧ (((p4 ∧ False) ∧ (p5 → p0)) → False)) ∧ ((((p7 → False) → False) → ((False ∧ p6) → False)) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        have assump_44 : (((p7 → False) → False) → ((False ∧ p6) → False)) := by
          intro assump_19
          intro assump_20
          cases assump_20
          case intro assump_21 assump_22 =>
            apply False.elim assump_21
        let assump_18 := assump_7 assump_44
        apply False.elim assump_18
      case inr assump_11 =>
        have assump_45 : (((p7 → False) → False) → ((False ∧ p6) → False)) := by
          intro assump_35
          intro assump_36
          cases assump_36
          case intro assump_37 assump_38 =>
            apply False.elim assump_37
        let assump_34 := assump_7 assump_45
        apply False.elim assump_34


variable (p3 p5 p4 p1 p6 p2 p7 : Prop)
theorem file96_68208 : (((((False ∧ False) → (p1 ∨ p5)) → ((p6 ∨ True) → (p5 ∨ p3))) → False) → ((((p6 → False) ∧ (p2 → False)) ∨ ((False → p7) ∧ (p2 ∧ p4))) → (((p1 → True) → (False ∧ p3)) → ((False → p4) ∨ (True ∧ p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      apply Or.inl
      intro assump_16
      apply False.elim assump_16
  case inr assump_7 =>
    cases assump_7
    case intro assump_19 assump_20 =>
      cases assump_20
      case intro assump_23 assump_24 =>
        apply Or.inl
        intro assump_31
        apply False.elim assump_31


variable (p5 p3 p6 p1 p4 : Prop)
theorem file96_68914 : (((((p1 → False) ∨ (p5 ∨ False)) ∧ ((p3 ∨ True) → False)) → (((p1 → False) → (True → False)) → ((True ∨ p1) → False))) ∨ ((((p3 ∧ p5) → False) ∨ ((p1 → p3) ∨ (p6 ∨ p4))) → False)) := by
  apply Or.inl
  intro assump_17
  intro assump_18
  intro assump_19
  cases assump_19
  case inl assump_20 =>
    cases assump_17
    case intro assump_26 assump_27 =>
      cases assump_26
      case inl assump_28 =>
        have assump_78 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_34 := assump_27 assump_78
        apply False.elim assump_34
      case inr assump_29 =>
        cases assump_29
        case inl assump_38 =>
          have assump_79 : (p3 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_44 := assump_27 assump_79
          apply False.elim assump_44
        case inr assump_39 =>
          apply False.elim assump_39
  case inr assump_21 =>
    cases assump_17
    case intro assump_54 assump_55 =>
      cases assump_54
      case inl assump_56 =>
        have assump_80 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_62 := assump_55 assump_80
        apply False.elim assump_62
      case inr assump_57 =>
        cases assump_57
        case inl assump_66 =>
          have assump_81 : (p3 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_72 := assump_55 assump_81
          apply False.elim assump_72
        case inr assump_67 =>
          apply False.elim assump_67


variable (p5 p4 p0 p2 p1 p6 p7 : Prop)
theorem file96_70524 : (((((p2 → False) ∨ (p1 ∧ p4)) → ((p7 → False) → False)) ∧ (((p1 ∧ p5) → (p0 ∨ p2)) ∧ ((p4 → p6) ∧ (False ∧ p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_14


variable (p5 p6 p2 p4 p3 p1 p0 : Prop)
theorem file96_71003 : (((((p3 ∨ p4) ∨ (p0 ∧ p4)) → ((p2 → p4) ∨ (p3 → p6))) → (((p6 ∧ p3) ∧ (p2 → False)) ∧ ((p1 ∨ p0) → False))) → ((((p5 ∧ p6) → False) → ((p2 ∧ p0) ∨ (p3 → p3))) ∨ (((p3 ∧ p2) ∨ (p5 ∨ p4)) ∧ ((p0 → False) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inr
  intro assump_7
  exact assump_7


variable (p3 p0 p1 p7 p6 : Prop)
theorem file96_71378 : (((((True ∧ p0) ∧ (p0 → False)) ∨ ((p6 ∧ p7) ∧ (p1 → False))) → False) → ((((p7 → p1) → (p3 → False)) ∨ ((p6 ∧ True) → False)) → (((False → True) ∨ (True ∧ p1)) ∨ ((False ∨ True) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_9
    apply True.intro
  case inr assump_4 =>
    apply Or.inl
    apply Or.inl
    intro assump_14
    apply True.intro


variable (p7 p0 p3 p6 p4 p2 p1 : Prop)
theorem file96_71884 : ((((((p2 ∨ p7) ∧ (p0 → p7)) → False) ∧ (((False ∨ p6) ∧ (p4 ∧ p2)) → False)) ∧ ((((False ∧ p6) ∧ (p3 ∧ p1)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_23 : (((False ∧ p6) ∧ (p3 ∧ p1)) → False) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
      let assump_12 := assump_3 assump_23
      apply False.elim assump_12


variable (p5 p3 p2 p7 p4 p6 p0 p1 : Prop)
theorem file96_72555 : ((((((False ∧ False) → (p6 → p7)) → ((True → False) ∨ (p1 → False))) → (((True ∨ p6) → (p7 → p2)) ∨ ((p3 → False) → False))) ∧ ((((p0 → p4) → False) ∨ ((p7 → p1) → (p5 ∨ p7))) ∧ (((True → False) ∧ (p5 ∧ p2)) ∧ ((p6 → p3) ∧ (p0 → False))))) → False) := by
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
            cases assump_15
            case intro assump_18 assump_19 =>
              cases assump_13
              case intro assump_24 assump_25 =>
                have assump_66 : True := by
                  apply True.intro
                let assump_34 := assump_14 assump_66
                apply False.elim assump_34
      case inr assump_9 =>
        cases assump_7
        case intro assump_40 assump_41 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            cases assump_43
            case intro assump_46 assump_47 =>
              cases assump_41
              case intro assump_52 assump_53 =>
                have assump_67 : True := by
                  apply True.intro
                let assump_62 := assump_42 assump_67
                apply False.elim assump_62


variable (p5 p1 p4 p0 p2 p7 : Prop)
theorem file96_73992 : (((((p5 → p7) ∨ (p7 → False)) ∧ ((p7 ∧ p4) → (False ∨ p1))) → (((p2 ∧ p1) ∧ (p7 ∧ False)) ∧ ((p0 ∨ p0) ∧ (p7 ∧ p1)))) → ((((p5 ∧ False) → False) ∨ ((p5 → p1) → False)) ∨ (((p2 → False) → False) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p7 p2 p4 p0 p6 p3 p5 : Prop)
theorem file96_74411 : (((((p5 ∨ p5) ∧ (p3 ∧ False)) ∧ ((p5 → False) → (p4 → True))) → (((p0 ∨ p2) ∨ (False ∧ p5)) → False)) ∨ ((((p7 ∨ p0) → False) → ((p6 ∨ p4) ∨ (True → False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_11
          case inl assump_13 =>
            cases assump_12
            case intro assump_17 assump_18 =>
              apply False.elim assump_18
          case inr assump_14 =>
            cases assump_12
            case intro assump_25 assump_26 =>
              apply False.elim assump_26
    case inr assump_6 =>
      cases assump_1
      case intro assump_33 assump_34 =>
        cases assump_33
        case intro assump_35 assump_36 =>
          cases assump_35
          case inl assump_37 =>
            cases assump_36
            case intro assump_41 assump_42 =>
              apply False.elim assump_42
          case inr assump_38 =>
            cases assump_36
            case intro assump_49 assump_50 =>
              apply False.elim assump_50
  case inr assump_4 =>
    cases assump_4
    case intro assump_55 assump_56 =>
      apply False.elim assump_55


variable (p5 p0 p4 p7 : Prop)
theorem file96_75802 : ((((((p5 → False) → (p4 ∨ False)) → False) → (((p7 ∧ True) ∧ (p0 → False)) → ((p0 → p0) → False))) ∧ ((((False → False) → False) → False) → False)) → False) := by
  intro assump_240
  cases assump_240
  case intro assump_241 assump_242 =>
    have assump_261 : (((False → False) → False) → False) := by
      intro assump_248
      have assump_262 : (False → False) := by
        intro assump_252
        apply False.elim assump_252
      let assump_251 := assump_248 assump_262
      apply False.elim assump_251
    let assump_247 := assump_242 assump_261
    apply False.elim assump_247


variable (p5 p2 p7 p1 p6 p4 p0 : Prop)
theorem file96_76454 : (((((p0 → False) ∧ (True → p1)) → False) → (((p7 ∧ p0) → (p5 → p5)) ∨ ((p1 → p2) → False))) ∨ ((((False → True) ∧ (False → False)) ∧ ((p5 ∨ p4) ∧ (p0 → p6))) → False)) := by
  apply Or.inl
  intro assump_27
  apply Or.inl
  intro assump_30
  intro assump_31
  cases assump_30
  case intro assump_34 assump_35 =>
    exact assump_31


variable (p0 p3 p7 p1 p5 p6 : Prop)
theorem file96_76846 : (((((False ∨ True) → False) → False) → False) → ((((p5 → p1) ∧ (p0 ∨ False)) ∨ ((True → True) ∨ (p6 → False))) → (((p7 → False) ∧ (p6 → False)) ∨ ((p1 ∧ p3) ∨ (False → p6))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case inl assump_9 =>
        apply Or.inl
        apply And.intro
        intro assump_15
        have assump_117 : (((False ∨ True) → False) → False) := by
          intro assump_20
          have assump_118 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_23 := assump_20 assump_118
          apply False.elim assump_23
        let assump_19 := assump_1 assump_117
        apply False.elim assump_19
        intro assump_30
        have assump_119 : (((False ∨ True) → False) → False) := by
          intro assump_35
          have assump_120 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_38 := assump_35 assump_120
          apply False.elim assump_38
        let assump_34 := assump_1 assump_119
        apply False.elim assump_34
      case inr assump_10 =>
        apply False.elim assump_10
  case inr assump_4 =>
    cases assump_4
    case inl assump_47 =>
      apply Or.inl
      apply And.intro
      intro assump_53
      have assump_121 : (((False ∨ True) → False) → False) := by
        intro assump_58
        have assump_122 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_61 := assump_58 assump_122
        apply False.elim assump_61
      let assump_57 := assump_1 assump_121
      apply False.elim assump_57
      intro assump_68
      have assump_123 : (((False ∨ True) → False) → False) := by
        intro assump_73
        have assump_124 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_76 := assump_73 assump_124
        apply False.elim assump_76
      let assump_72 := assump_1 assump_123
      apply False.elim assump_72
    case inr assump_48 =>
      apply Or.inl
      apply And.intro
      intro assump_87
      have assump_125 : (((False ∨ True) → False) → False) := by
        intro assump_92
        have assump_126 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_95 := assump_92 assump_126
        apply False.elim assump_95
      let assump_91 := assump_1 assump_125
      apply False.elim assump_91
      intro assump_102
      have assump_127 : (((False ∨ True) → False) → False) := by
        intro assump_107
        have assump_128 : (False ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_110 := assump_107 assump_128
        apply False.elim assump_110
      let assump_106 := assump_1 assump_127
      apply False.elim assump_106


variable (p2 p4 : Prop)
theorem file96_79774 : ((((((p2 ∨ True) → (p4 → True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p2 ∨ True) → (p4 → True)) → False) → False) := by
    intro assump_5
    have assump_18 : ((p2 ∨ True) → (p4 → True)) := by
      intro assump_9
      intro assump_10
      apply True.intro
    let assump_8 := assump_5 assump_18
    apply False.elim assump_8
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p6 p5 p1 p7 p4 p3 p2 : Prop)
theorem file96_80275 : (((((p2 ∨ p1) ∧ (True → False)) ∧ ((p1 → False) ∧ (True → p5))) → False) ∧ ((((False ∧ p6) → False) ∨ ((p7 ∧ p3) → (p7 → False))) ∨ (((p4 ∨ p4) → False) ∧ ((p1 → False) → False)))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          have assump_46 : True := by
            apply True.intro
          let assump_21 := assump_5 assump_46
          apply False.elim assump_21
      case inr assump_7 =>
        cases assump_3
        case intro assump_29 assump_30 =>
          have assump_47 : p1 := by
            exact assump_7
          let assump_37 := assump_29 assump_47
          apply False.elim assump_37
  apply Or.inl
  apply Or.inl
  intro assump_41
  cases assump_41
  case intro assump_42 assump_43 =>
    apply False.elim assump_42


variable (p4 p2 p6 p0 p7 p1 p5 : Prop)
theorem file96_81301 : ((((((False ∧ True) ∧ (p6 → False)) ∧ ((p0 ∧ False) → (True → p5))) ∧ (((p6 → True) → False) → False)) ∧ ((((p4 ∧ False) → (p5 ∧ p7)) ∨ ((p5 ∧ p0) ∨ (p6 ∧ p2))) ∧ (((p2 ∧ p6) → (p1 → False)) → False))) → False) := by
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
            apply False.elim assump_10


variable (p2 p3 p6 p7 : Prop)
theorem file96_81925 : ((((((p2 ∧ False) → (p6 → p3)) ∨ ((p3 → False) ∨ (p7 → False))) ∨ (((p2 → False) → (p2 → True)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p2 ∧ False) → (p6 → p3)) ∨ ((p3 → False) ∨ (p7 → False))) ∨ (((p2 → False) → (p2 → True)) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p5 p2 p6 p4 : Prop)
theorem file96_82484 : ((((((True ∨ p6) → False) → ((False ∨ p4) → (p3 → False))) ∨ (((p5 ∨ False) ∨ (p2 → False)) ∧ ((p5 ∧ p2) ∧ (False → p4)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True ∨ p6) → False) → ((False ∨ p4) → (p3 → False))) ∨ (((p5 ∨ False) ∨ (p2 → False)) ∧ ((p5 ∧ p2) ∧ (False → p4)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      apply False.elim assump_10
    case inr assump_11 =>
      have assump_26 : (True ∨ p6) := by
        apply Or.inl
        apply True.intro
      let assump_18 := assump_5 assump_26
      apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p0 p5 p1 p7 p4 p6 p2 p3 : Prop)
theorem file96_83265 : ((((((p3 ∧ p1) ∨ (p7 → p3)) → False) → False) ∧ ((((p2 ∧ p5) ∨ (True → p7)) ∨ ((p4 ∧ True) → (p0 ∧ p5))) ∧ (((p6 ∨ p7) ∨ (False → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            have assump_49 : ((p6 ∨ p7) ∨ (False → False)) := by
              apply Or.inr
              intro assump_21
              apply False.elim assump_21
            let assump_20 := assump_7 assump_49
            apply False.elim assump_20
        case inr assump_11 =>
          have assump_50 : ((p6 ∨ p7) ∨ (False → False)) := by
            apply Or.inr
            intro assump_32
            apply False.elim assump_32
          let assump_31 := assump_7 assump_50
          apply False.elim assump_31
      case inr assump_9 =>
        have assump_51 : ((p6 ∨ p7) ∨ (False → False)) := by
          apply Or.inr
          intro assump_43
          apply False.elim assump_43
        let assump_42 := assump_7 assump_51
        apply False.elim assump_42


variable (p1 p6 : Prop)
theorem file96_84542 : (((((True ∨ p6) → False) → ((p1 → False) → (False → False))) → False) → False) := by
  intro assump_1
  have assump_13 : (((True ∨ p6) → False) → ((p1 → False) → (False → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p6 p3 p2 p0 p1 : Prop)
theorem file96_84937 : (((((True → False) → (p3 ∨ p0)) → ((False ∧ p1) ∧ (p6 → p3))) → False) ∨ ((((True → False) → False) ∨ ((True → False) ∨ (p2 ∧ False))) → False)) := by
  apply Or.inl
  intro assump_5
  have assump_21 : ((True → False) → (p3 ∨ p0)) := by
    intro assump_9
    have assump_22 : True := by
      apply True.intro
    let assump_12 := assump_9 assump_22
    apply False.elim assump_12
  let assump_8 := assump_5 assump_21
  let assump_16 := And.left assump_8
  let assump_17 := And.left assump_16
  apply False.elim assump_17


variable (p4 p1 p3 p7 : Prop)
theorem file96_85514 : ((((((False ∨ p7) → False) ∨ ((p4 ∧ True) → False)) ∨ (((p7 → p3) → False) → ((p1 → False) → False))) ∧ ((((False ∧ p1) ∧ (p4 → False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_53 : (((False ∧ p1) ∧ (p4 → False)) → False) := by
          intro assump_13
          cases assump_13
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
        let assump_12 := assump_3 assump_53
        apply False.elim assump_12
      case inr assump_7 =>
        have assump_54 : (((False ∧ p1) ∧ (p4 → False)) → False) := by
          intro assump_28
          cases assump_28
          case intro assump_29 assump_30 =>
            cases assump_29
            case intro assump_31 assump_32 =>
              apply False.elim assump_31
        let assump_27 := assump_3 assump_54
        apply False.elim assump_27
    case inr assump_5 =>
      have assump_55 : (((False ∧ p1) ∧ (p4 → False)) → False) := by
        intro assump_43
        cases assump_43
        case intro assump_44 assump_45 =>
          cases assump_44
          case intro assump_46 assump_47 =>
            apply False.elim assump_46
      let assump_42 := assump_3 assump_55
      apply False.elim assump_42


variable (p2 p4 p3 p7 p5 : Prop)
theorem file96_87018 : ((((((p4 ∨ True) ∨ (p3 ∨ p2)) → False) → (((p7 → False) ∨ (p4 → False)) → ((p4 ∨ p7) → (p2 ∨ False)))) → ((((p3 ∧ False) ∧ (p7 ∨ p5)) → False) → False)) → False) := by
  intro assump_22
  have assump_84 : ((((p4 ∨ True) ∨ (p3 ∨ p2)) → False) → (((p7 → False) ∨ (p4 → False)) → ((p4 ∨ p7) → (p2 ∨ False)))) := by
    intro assump_26
    intro assump_27
    intro assump_28
    cases assump_28
    case inl assump_29 =>
      cases assump_27
      case inl assump_33 =>
        have assump_85 : ((p4 ∨ True) ∨ (p3 ∨ p2)) := by
          apply Or.inl
          apply Or.inl
          exact assump_29
        let assump_39 := assump_26 assump_85
        apply False.elim assump_39
      case inr assump_34 =>
        have assump_86 : ((p4 ∨ True) ∨ (p3 ∨ p2)) := by
          apply Or.inl
          apply Or.inl
          exact assump_29
        let assump_47 := assump_26 assump_86
        apply False.elim assump_47
    case inr assump_30 =>
      cases assump_27
      case inl assump_53 =>
        have assump_87 : ((p4 ∨ True) ∨ (p3 ∨ p2)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_59 := assump_26 assump_87
        apply False.elim assump_59
      case inr assump_54 =>
        have assump_88 : ((p4 ∨ True) ∨ (p3 ∨ p2)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_67 := assump_26 assump_88
        apply False.elim assump_67
  let assump_25 := assump_22 assump_84
  have assump_89 : (((p3 ∧ False) ∧ (p7 ∨ p5)) → False) := by
    intro assump_72
    cases assump_72
    case intro assump_73 assump_74 =>
      cases assump_73
      case intro assump_75 assump_76 =>
        apply False.elim assump_76
  let assump_71 := assump_25 assump_89
  apply False.elim assump_71


variable (p2 p5 p3 p7 p4 p0 p1 p6 : Prop)
theorem file96_88866 : ((((((False ∨ p7) ∧ (p3 ∨ p0)) ∧ ((p5 ∧ p7) ∧ (p6 ∨ True))) → (((p6 ∨ p1) → (True ∨ p7)) ∧ ((p4 → True) ∨ (p2 ∨ p6)))) ∧ ((((p4 ∧ p4) → (p4 → True)) → ((p7 → False) → False)) ∧ (((True → p4) ∨ (True → p5)) ∧ ((p6 ∧ p4) ∧ (False ∧ p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_17
              case intro assump_24 assump_25 =>
                apply False.elim assump_24
        case inr assump_13 =>
          cases assump_11
          case intro assump_30 assump_31 =>
            cases assump_30
            case intro assump_32 assump_33 =>
              cases assump_31
              case intro assump_38 assump_39 =>
                apply False.elim assump_38


variable (p1 p2 p0 p7 p5 p4 : Prop)
theorem file96_89977 : ((((((p1 → False) ∧ (p0 → False)) ∧ ((p7 → p1) → False)) → (((p2 → False) → (False ∧ p7)) ∨ ((p2 ∧ p5) → False))) ∧ ((((p2 → p5) → False) → ((p7 ∧ p4) → (p5 → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((p2 → p5) → False) → ((p7 ∧ p4) → (p5 → p7))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      cases assump_10
      case intro assump_14 assump_15 =>
        exact assump_14
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p4 p0 p7 p3 p2 p1 p5 p6 : Prop)
theorem file96_90596 : ((((((p7 → p6) → (p5 ∧ p6)) → ((p4 → p7) → (p2 ∨ p6))) ∧ (((p0 ∧ p6) → (p6 ∨ False)) ∧ ((p0 → p6) ∧ (p1 → False)))) ∧ ((((p3 → False) → (p6 → p6)) ∨ ((p6 ∧ p1) → (False → p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          have assump_30 : (((p3 → False) → (p6 → p6)) ∨ ((p6 ∧ p1) → (False → p1))) := by
            apply Or.inl
            intro assump_21
            intro assump_22
            exact assump_22
          let assump_20 := assump_3 assump_30
          apply False.elim assump_20


variable (p2 p0 p4 p1 p3 p7 p6 : Prop)
theorem file96_91391 : (((((True → False) ∨ (True ∧ True)) ∧ ((True → p1) ∨ (False → p0))) → (((False ∨ True) ∨ (False ∨ p1)) ∨ ((p4 ∨ True) → (p2 → p7)))) ∨ ((((p3 → False) → False) ∧ ((p1 ∧ p0) → (p3 ∨ p6))) → (((p1 → p7) → False) ∨ ((False ∨ False) → (p3 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_9 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
    case inr assump_5 =>
      cases assump_5
      case intro assump_14 assump_15 =>
        cases assump_3
        case inl assump_20 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_21 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          apply True.intro


variable (p1 p0 p3 : Prop)
theorem file96_92435 : (((((p1 ∨ p3) ∨ (False ∧ p0)) → ((p1 ∧ p0) → (p1 ∧ p1))) → False) → False) := by
  intro assump_1
  have assump_46 : (((p1 ∨ p3) ∨ (False ∧ p0)) → ((p1 ∧ p0) → (p1 ∧ p1))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case inl assump_13 =>
        cases assump_13
        case inl assump_15 =>
          exact assump_15
        case inr assump_16 =>
          exact assump_7
      case inr assump_14 =>
        cases assump_14
        case intro assump_21 assump_22 =>
          apply False.elim assump_21
    cases assump_6
    case intro assump_25 assump_26 =>
      cases assump_5
      case inl assump_31 =>
        cases assump_31
        case inl assump_33 =>
          exact assump_33
        case inr assump_34 =>
          exact assump_25
      case inr assump_32 =>
        cases assump_32
        case intro assump_39 assump_40 =>
          apply False.elim assump_39
  let assump_4 := assump_1 assump_46
  apply False.elim assump_4


variable (p0 p6 p2 p3 p1 p5 p4 : Prop)
theorem file96_93542 : ((((((p3 → False) → False) ∨ ((False ∨ p4) ∧ (p4 → False))) → (((False ∨ p5) → (p0 ∧ p4)) ∨ ((p2 → p6) → (p2 ∧ p2)))) ∧ ((((p1 ∧ p4) → (p6 ∨ True)) ∨ ((p5 → p0) ∧ (p5 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p1 ∧ p4) → (p6 ∨ True)) ∨ ((p5 → p0) ∧ (p5 → False))) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inr
        apply True.intro
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p1 p4 p3 p7 p6 p5 p2 : Prop)
theorem file96_94176 : (((((p2 → False) → False) → ((p4 → True) → False)) → False) → ((((False → p4) ∨ (p6 → False)) → ((False ∨ p1) → (p3 → p3))) ∨ (((p7 ∨ p1) ∨ (p4 → False)) → ((True → p5) ∧ (p5 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_5
  case inl assump_9 =>
    apply False.elim assump_9
  case inr assump_10 =>
    cases assump_4
    case inl assump_15 =>
      exact assump_6
    case inr assump_16 =>
      exact assump_6


variable (p2 p3 p7 p5 p1 p0 : Prop)
theorem file96_94720 : ((((((p3 → p5) ∧ (p2 ∨ p2)) → ((p0 → False) → (False → False))) ∨ (((p3 ∨ p0) → (p0 ∨ p7)) ∨ ((p7 → p1) ∨ (True ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p3 → p5) ∧ (p2 ∨ p2)) → ((p0 → False) → (False → False))) ∨ (((p3 ∨ p0) → (p0 ∨ p7)) ∨ ((p7 → p1) ∨ (True ∨ p3)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p5 p4 p0 p7 p3 p1 : Prop)
theorem file96_95255 : (((((p5 ∨ p0) → (p0 → True)) → False) → (((False ∨ p3) ∧ (False ∨ p4)) ∧ ((p0 → False) ∨ (p4 → False)))) ∨ ((((p5 → p1) → (p7 → p0)) → ((False ∨ p7) → (p1 ∨ p1))) → (((p3 ∧ p0) → False) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  have assump_30 : ((p5 ∨ p0) → (p0 → True)) := by
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4
  have assump_31 : ((p5 ∨ p0) → (p0 → True)) := by
    intro assump_13
    intro assump_14
    apply True.intro
  let assump_12 := assump_1 assump_31
  apply False.elim assump_12
  apply Or.inl
  intro assump_20
  have assump_32 : ((p5 ∨ p0) → (p0 → True)) := by
    intro assump_25
    intro assump_26
    apply True.intro
  let assump_24 := assump_1 assump_32
  apply False.elim assump_24


variable (p6 p7 p3 p0 p1 p4 p2 p5 : Prop)
theorem file96_96158 : (((((p5 → False) → False) ∧ ((p3 → False) ∨ (p1 → False))) ∨ (((p7 ∧ p2) → False) ∨ ((p3 → p2) → (p1 → p6)))) → ((((p4 → False) → (True → False)) → ((True ∨ p5) → (False ∨ True))) ∨ (((p2 ∨ True) ∧ (p5 ∨ p0)) ∨ ((p1 → False) → (p5 ∨ True))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        intro assump_13
        cases assump_13
        case inl assump_14 =>
          apply Or.inr
          apply True.intro
        case inr assump_15 =>
          apply Or.inr
          apply True.intro
      case inr assump_9 =>
        apply Or.inl
        intro assump_26
        intro assump_27
        cases assump_27
        case inl assump_28 =>
          apply Or.inr
          apply True.intro
        case inr assump_29 =>
          apply Or.inr
          apply True.intro
  case inr assump_3 =>
    cases assump_3
    case inl assump_38 =>
      apply Or.inl
      intro assump_42
      intro assump_43
      cases assump_43
      case inl assump_44 =>
        apply Or.inr
        apply True.intro
      case inr assump_45 =>
        apply Or.inr
        apply True.intro
    case inr assump_39 =>
      apply Or.inl
      intro assump_56
      intro assump_57
      cases assump_57
      case inl assump_58 =>
        apply Or.inr
        apply True.intro
      case inr assump_59 =>
        apply Or.inr
        apply True.intro


variable (p5 p7 p2 : Prop)
theorem file96_97711 : (((((p7 → p2) → False) → ((False → False) ∨ (p5 → False))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p7 → p2) → False) → ((False → False) ∨ (p5 → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p0 p2 p6 p3 p4 p7 p5 : Prop)
theorem file96_98106 : (((((False → p6) → False) → False) → False) → ((((p5 ∧ p5) ∨ (p3 ∨ False)) → False) ∧ (((p0 → False) ∨ (p6 ∧ p7)) ∧ ((True ∧ False) ∨ (p2 ∧ p4))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      have assump_85 : (((False → p6) → False) → False) := by
        intro assump_14
        have assump_86 : (False → p6) := by
          intro assump_18
          apply False.elim assump_18
        let assump_17 := assump_14 assump_86
        apply False.elim assump_17
      let assump_13 := assump_1 assump_85
      apply False.elim assump_13
  case inr assump_4 =>
    cases assump_4
    case inl assump_27 =>
      have assump_87 : (((False → p6) → False) → False) := by
        intro assump_34
        have assump_88 : (False → p6) := by
          intro assump_38
          apply False.elim assump_38
        let assump_37 := assump_34 assump_88
        apply False.elim assump_37
      let assump_33 := assump_1 assump_87
      apply False.elim assump_33
    case inr assump_28 =>
      apply False.elim assump_28
  apply And.intro
  apply Or.inl
  intro assump_51
  have assump_89 : (((False → p6) → False) → False) := by
    intro assump_56
    have assump_90 : (False → p6) := by
      intro assump_60
      apply False.elim assump_60
    let assump_59 := assump_56 assump_90
    apply False.elim assump_59
  let assump_55 := assump_1 assump_89
  apply False.elim assump_55
  have assump_91 : (((False → p6) → False) → False) := by
    intro assump_72
    have assump_92 : (False → p6) := by
      intro assump_76
      apply False.elim assump_76
    let assump_75 := assump_72 assump_92
    apply False.elim assump_75
  let assump_71 := assump_1 assump_91
  apply False.elim assump_71


variable (p2 p3 p5 p6 p7 p4 : Prop)
theorem file96_99965 : ((((((p6 ∨ True) ∨ (True ∧ p7)) ∨ ((p5 ∧ False) → (p7 ∨ True))) → False) ∨ ((((p5 → p7) ∨ (p2 → False)) ∧ ((p7 ∧ False) ∧ (True → p4))) ∨ (((p3 → False) → (p2 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_44 : (((p6 ∨ True) ∨ (True ∧ p7)) ∨ ((p5 ∧ False) → (p7 ∨ True))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_6 := assump_2 assump_44
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_13
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              apply False.elim assump_21
        case inr assump_15 =>
          cases assump_13
          case intro assump_28 assump_29 =>
            cases assump_28
            case intro assump_30 assump_31 =>
              apply False.elim assump_31
    case inr assump_11 =>
      have assump_45 : ((p3 → False) → (p2 → True)) := by
        intro assump_39
        intro assump_40
        apply True.intro
      let assump_38 := assump_11 assump_45
      apply False.elim assump_38


variable (p1 p2 p3 p6 p4 p5 : Prop)
theorem file96_101330 : (((((True ∨ False) ∧ (p3 ∨ p2)) ∨ ((True ∧ p5) → (p6 ∨ p5))) → (((True ∨ False) ∨ (p3 → False)) → ((p3 ∨ True) → (True → p6)))) → ((((p5 → p3) ∨ (p4 → p5)) ∧ ((p4 → False) ∧ (p2 → False))) → (((p1 ∧ p2) → False) ∨ ((p2 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        apply Or.inl
        intro assump_17
        cases assump_17
        case intro assump_18 assump_19 =>
          have assump_63 : p2 := by
            exact assump_19
          let assump_31 := assump_10 assump_63
          apply False.elim assump_31
    case inr assump_6 =>
      cases assump_4
      case intro assump_37 assump_38 =>
        apply Or.inl
        intro assump_45
        cases assump_45
        case intro assump_46 assump_47 =>
          have assump_64 : p2 := by
            exact assump_47
          let assump_59 := assump_38 assump_64
          apply False.elim assump_59


variable (p1 p3 p2 p6 p0 p7 : Prop)
theorem file96_102429 : ((((((p2 → p0) ∧ (p2 ∧ False)) ∧ ((p6 → p7) ∨ (p3 → False))) → False) ∧ ((((p6 ∧ False) → False) ∨ ((p1 → p0) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p6 ∧ False) → False) ∨ ((p1 → p0) → False)) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p3 p2 p0 p7 p5 p4 p1 : Prop)
theorem file96_102984 : ((((((p5 ∨ p3) ∨ (p1 ∧ True)) ∨ ((p1 → p4) ∨ (True → False))) ∨ (((p2 → False) ∨ (p7 ∨ p7)) → ((p4 ∧ p0) ∧ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p5 ∨ p3) ∨ (p1 ∧ True)) ∨ ((p1 → p4) ∨ (True → False))) ∨ (((p2 → False) ∨ (p7 ∨ p7)) → ((p4 ∧ p0) ∧ (p2 → False)))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    intro assump_5
    have assump_17 : ((((p5 ∨ p3) ∨ (p1 ∧ True)) ∨ ((p1 → p4) ∨ (True → False))) ∨ (((p2 → False) ∨ (p7 ∨ p7)) → ((p4 ∧ p0) ∧ (p2 → False)))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply And.intro
      exact assump_5
      apply True.intro
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p0 p3 : Prop)
theorem file96_103817 : ((((((False → False) → False) → False) ∨ (((p0 → p3) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) → False) → False) ∨ (((p0 → p3) → False) → False)) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p6 p1 p7 p2 p4 p3 : Prop)
theorem file96_104354 : (((((True → p7) → (p4 ∨ p7)) → ((p2 ∧ p3) ∨ (p7 → False))) ∨ (((p1 ∧ p0) → (True ∨ p2)) → False)) → ((((p7 → False) ∧ (p1 → p3)) → False) → (((p4 → p4) ∧ (p1 ∨ False)) ∨ ((False → p6) ∧ (False → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inr
    apply And.intro
    intro assump_12
    apply False.elim assump_12
    intro assump_15
    apply False.elim assump_15
  case inr assump_6 =>
    apply Or.inr
    apply And.intro
    intro assump_23
    apply False.elim assump_23
    intro assump_26
    apply False.elim assump_26


variable (p3 p0 p2 p5 p7 p6 : Prop)
theorem file96_105001 : (((((p5 ∨ p0) → (True → p2)) ∧ ((p5 ∨ True) ∨ (p6 ∧ p0))) ∧ (((p2 ∧ p3) ∧ (p7 → False)) ∧ ((p3 ∨ p5) → (p2 → False)))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_11
      case inl assump_14 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_9
          case intro assump_20 assump_21 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              cases assump_22
              case intro assump_24 assump_25 =>
                have assump_85 : (p3 ∨ p5) := by
                  apply Or.inl
                  exact assump_25
                let assump_34 := assump_21 assump_85
                have assump_86 : p2 := by
                  exact assump_24
                let assump_35 := assump_34 assump_86
                apply False.elim assump_35
        case inr assump_17 =>
          cases assump_9
          case intro assump_41 assump_42 =>
            cases assump_41
            case intro assump_43 assump_44 =>
              cases assump_43
              case intro assump_45 assump_46 =>
                have assump_87 : (p3 ∨ p5) := by
                  apply Or.inl
                  exact assump_46
                let assump_55 := assump_42 assump_87
                have assump_88 : p2 := by
                  exact assump_45
                let assump_56 := assump_55 assump_88
                apply False.elim assump_56
      case inr assump_15 =>
        cases assump_15
        case intro assump_60 assump_61 =>
          cases assump_9
          case intro assump_66 assump_67 =>
            cases assump_66
            case intro assump_68 assump_69 =>
              cases assump_68
              case intro assump_70 assump_71 =>
                have assump_89 : (p3 ∨ p5) := by
                  apply Or.inl
                  exact assump_71
                let assump_80 := assump_67 assump_89
                have assump_90 : p2 := by
                  exact assump_70
                let assump_81 := assump_80 assump_90
                apply False.elim assump_81


