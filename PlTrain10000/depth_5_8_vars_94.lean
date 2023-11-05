variable (p6 p0 p1 p7 p2 : Prop)
theorem file94_41 : (((((True → False) ∧ (False ∨ p1)) ∧ ((p7 ∨ True) → (p2 → p0))) ∧ (((p6 ∧ False) → (True ∧ p1)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          apply False.elim assump_10
        case inr assump_11 =>
          have assump_31 : ((p6 ∧ False) → (True ∧ p1)) := by
            intro assump_21
            apply And.intro
            apply True.intro
            cases assump_21
            case intro assump_22 assump_23 =>
              apply False.elim assump_23
          let assump_20 := assump_3 assump_31
          apply False.elim assump_20


variable (p3 p5 p2 p7 p4 : Prop)
theorem file94_866 : (((((True → False) → False) → ((False ∧ p2) ∧ (p5 ∧ p4))) ∧ (((p7 ∨ p3) ∧ (p5 ∧ p3)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : ((True → False) → False) := by
      intro assump_10
      have assump_23 : True := by
        apply True.intro
      let assump_13 := assump_10 assump_23
      apply False.elim assump_13
    let assump_9 := assump_2 assump_22
    let assump_17 := And.left assump_9
    let assump_18 := And.left assump_17
    apply False.elim assump_18


variable (p5 p4 p3 : Prop)
theorem file94_1453 : ((((((True → p3) ∨ (p5 ∨ True)) → ((False → False) ∨ (p4 ∨ True))) ∧ (((False → False) ∧ (p5 ∧ False)) → False)) → False) → False) := by
  intro assump_10
  have assump_48 : ((((True → p3) ∨ (p5 ∨ True)) → ((False → False) ∨ (p4 ∨ True))) ∧ (((False → False) ∧ (p5 ∧ False)) → False)) := by
    apply And.intro
    intro assump_14
    cases assump_14
    case inl assump_15 =>
      apply Or.inl
      intro assump_19
      apply False.elim assump_19
    case inr assump_16 =>
      cases assump_16
      case inl assump_22 =>
        apply Or.inl
        intro assump_26
        apply False.elim assump_26
      case inr assump_23 =>
        apply Or.inl
        intro assump_31
        apply False.elim assump_31
    intro assump_34
    cases assump_34
    case intro assump_35 assump_36 =>
      cases assump_36
      case intro assump_39 assump_40 =>
        apply False.elim assump_40
  let assump_13 := assump_10 assump_48
  apply False.elim assump_13


variable (p1 p0 p2 p5 p6 p3 p7 p4 : Prop)
theorem file94_2477 : (((((p5 → p5) → (p1 → p1)) → False) → (((p2 ∨ False) → (p3 → p6)) → ((p5 → p4) ∨ (p1 ∧ p5)))) ∨ ((((p6 → False) ∨ (p6 ∨ p4)) → ((p4 ∧ p7) ∨ (p4 ∧ p7))) ∨ (((p6 → False) ∨ (True ∧ p5)) → ((p1 ∨ False) ∨ (p6 ∨ p0))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  have assump_21 : ((p5 → p5) → (p1 → p1)) := by
    intro assump_12
    intro assump_13
    exact assump_13
  let assump_11 := assump_1 assump_21
  apply False.elim assump_11


variable (p6 p0 p7 p3 p5 p4 p1 : Prop)
theorem file94_3019 : (((((False ∨ p6) → (p7 → False)) ∨ ((p0 ∨ p4) → (False → False))) ∨ (((p0 ∨ p4) ∨ (p3 → False)) → ((False → p1) ∨ (p3 → p7)))) → ((((p4 ∧ p1) ∨ (p1 ∧ False)) ∧ ((False ∧ p6) ∨ (True ∨ p5))) ∨ (((False → p5) → (True → False)) → ((p7 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inr
      intro assump_8
      intro assump_9
      have assump_54 : (False → p5) := by
        intro assump_15
        apply False.elim assump_15
      let assump_14 := assump_8 assump_54
      have assump_55 : True := by
        apply True.intro
      let assump_18 := assump_14 assump_55
      apply False.elim assump_18
    case inr assump_5 =>
      apply Or.inr
      intro assump_24
      intro assump_25
      have assump_56 : (False → p5) := by
        intro assump_31
        apply False.elim assump_31
      let assump_30 := assump_24 assump_56
      have assump_57 : True := by
        apply True.intro
      let assump_34 := assump_30 assump_57
      apply False.elim assump_34
  case inr assump_3 =>
    apply Or.inr
    intro assump_40
    intro assump_41
    have assump_58 : (False → p5) := by
      intro assump_47
      apply False.elim assump_47
    let assump_46 := assump_40 assump_58
    have assump_59 : True := by
      apply True.intro
    let assump_50 := assump_46 assump_59
    apply False.elim assump_50


variable (p2 p7 p1 p3 p4 p5 : Prop)
theorem file94_4488 : ((((((p5 ∧ p2) ∧ (p4 ∧ p2)) → ((p4 ∨ True) ∨ (p5 → False))) ∧ (((False → p7) → False) → ((p1 ∧ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_40 : ((((p5 ∧ p2) ∧ (p4 ∧ p2)) → ((p4 ∨ True) ∨ (p5 → False))) ∧ (((False → p7) → False) → ((p1 ∧ p3) → False))) := by
    apply And.intro
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply Or.inl
          apply Or.inl
          exact assump_14
    intro assump_20
    intro assump_21
    cases assump_21
    case intro assump_22 assump_23 =>
      have assump_41 : (False → p7) := by
        intro assump_31
        apply False.elim assump_31
      let assump_30 := assump_20 assump_41
      apply False.elim assump_30
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p2 : Prop)
theorem file94_5447 : (((((p2 → True) → False) → False) → False) → False) := by
  intro assump_1
  have assump_16 : (((p2 → True) → False) → False) := by
    intro assump_5
    have assump_17 : (p2 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 p4 p0 p1 p3 p5 : Prop)
theorem file94_5875 : (((((False → False) ∧ (p1 → False)) ∨ ((True → False) → False)) → (((p4 ∧ False) → False) ∨ ((p6 ∨ p1) → (p6 ∨ p4)))) ∨ ((((False ∨ p5) ∨ (p3 ∨ p1)) → ((p1 → False) → (p0 → False))) ∧ (((False → False) ∧ (p3 → p6)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
  case inr assump_3 =>
    apply Or.inl
    intro assump_19
    cases assump_19
    case intro assump_20 assump_21 =>
      apply False.elim assump_21


variable (p4 p1 p6 p7 p5 p3 p2 p0 : Prop)
theorem file94_6589 : (((((p6 ∧ p2) ∧ (p3 ∧ True)) → ((p5 ∨ p7) ∧ (False ∨ False))) ∧ (((p4 ∨ p6) ∨ (p4 → False)) → False)) → ((((p2 → p0) ∧ (p1 ∧ p5)) → False) ∨ (((p6 → p7) → False) ∨ ((p4 → p2) ∧ (p3 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        have assump_37 : ((p4 ∨ p6) ∨ (p4 → False)) := by
          apply Or.inr
          intro assump_23
          have assump_38 : ((p4 ∨ p6) ∨ (p4 → False)) := by
            apply Or.inl
            apply Or.inl
            exact assump_23
          let assump_30 := assump_3 assump_38
          apply False.elim assump_30
        let assump_22 := assump_3 assump_37
        apply False.elim assump_22


variable (p4 p0 p6 p7 p3 p1 : Prop)
theorem file94_7478 : (((((True ∨ True) → False) → False) → False) → ((((p6 → True) → False) ∨ ((False ∨ p4) → (p4 ∧ p7))) → (((p0 ∨ p1) → (False ∨ p6)) ∧ ((p7 → p0) ∨ (p3 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      have assump_114 : (((True ∨ True) → False) → False) := by
        intro assump_15
        have assump_115 : (True ∨ True) := by
          apply Or.inl
          apply True.intro
        let assump_18 := assump_15 assump_115
        apply False.elim assump_18
      let assump_14 := assump_1 assump_114
      apply False.elim assump_14
    case inr assump_9 =>
      have assump_116 : (((True ∨ True) → False) → False) := by
        intro assump_30
        have assump_117 : (True ∨ True) := by
          apply Or.inl
          apply True.intro
        let assump_33 := assump_30 assump_117
        apply False.elim assump_33
      let assump_29 := assump_1 assump_116
      apply False.elim assump_29
  case inr assump_5 =>
    cases assump_2
    case inl assump_42 =>
      have assump_118 : (((True ∨ True) → False) → False) := by
        intro assump_49
        have assump_119 : (True ∨ True) := by
          apply Or.inl
          apply True.intro
        let assump_52 := assump_49 assump_119
        apply False.elim assump_52
      let assump_48 := assump_1 assump_118
      apply False.elim assump_48
    case inr assump_43 =>
      have assump_120 : (((True ∨ True) → False) → False) := by
        intro assump_64
        have assump_121 : (True ∨ True) := by
          apply Or.inl
          apply True.intro
        let assump_67 := assump_64 assump_121
        apply False.elim assump_67
      let assump_63 := assump_1 assump_120
      apply False.elim assump_63
  cases assump_2
  case inl assump_74 =>
    apply Or.inl
    intro assump_80
    have assump_122 : (((True ∨ True) → False) → False) := by
      intro assump_85
      have assump_123 : (True ∨ True) := by
        apply Or.inl
        apply True.intro
      let assump_88 := assump_85 assump_123
      apply False.elim assump_88
    let assump_84 := assump_1 assump_122
    apply False.elim assump_84
  case inr assump_75 =>
    apply Or.inl
    intro assump_99
    have assump_124 : (((True ∨ True) → False) → False) := by
      intro assump_104
      have assump_125 : (True ∨ True) := by
        apply Or.inl
        apply True.intro
      let assump_107 := assump_104 assump_125
      apply False.elim assump_107
    let assump_103 := assump_1 assump_124
    apply False.elim assump_103


variable (p1 p5 p4 p0 p6 p7 : Prop)
theorem file94_10134 : (((((p1 → False) → False) → ((False → p0) ∨ (p6 → p7))) → False) → ((((False ∧ p4) ∨ (p7 → False)) ∧ ((True → p7) → (p0 ∨ p5))) → False)) := by
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
      have assump_27 : (((p1 → False) → False) → ((False → p0) ∨ (p6 → p7))) := by
        intro assump_18
        apply Or.inl
        intro assump_21
        apply False.elim assump_21
      let assump_17 := assump_1 assump_27
      apply False.elim assump_17


variable (p0 p7 p1 p3 p5 p4 p2 p6 : Prop)
theorem file94_10853 : (((((p6 → p4) ∨ (p1 → False)) ∨ ((p1 → True) ∨ (False ∨ p3))) ∧ (((p4 ∧ p5) → (p6 → False)) ∧ ((p0 → p6) ∧ (p0 ∧ p0)))) → ((((p7 ∧ False) → (True → p2)) ∨ ((p7 → p6) → (p6 ∨ p1))) ∨ (((p0 → p1) ∨ (False ∧ p2)) → ((p1 ∨ p7) → (True ∧ False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              apply Or.inl
              apply Or.inl
              intro assump_24
              intro assump_25
              cases assump_24
              case intro assump_28 assump_29 =>
                apply False.elim assump_29
      case inr assump_7 =>
        cases assump_3
        case intro assump_36 assump_37 =>
          cases assump_37
          case intro assump_40 assump_41 =>
            cases assump_41
            case intro assump_44 assump_45 =>
              apply Or.inl
              apply Or.inl
              intro assump_50
              intro assump_51
              cases assump_50
              case intro assump_54 assump_55 =>
                apply False.elim assump_55
    case inr assump_5 =>
      cases assump_5
      case inl assump_60 =>
        cases assump_3
        case intro assump_64 assump_65 =>
          cases assump_65
          case intro assump_68 assump_69 =>
            cases assump_69
            case intro assump_72 assump_73 =>
              apply Or.inl
              apply Or.inl
              intro assump_78
              intro assump_79
              cases assump_78
              case intro assump_82 assump_83 =>
                apply False.elim assump_83
      case inr assump_61 =>
        cases assump_61
        case inl assump_88 =>
          apply False.elim assump_88
        case inr assump_89 =>
          cases assump_3
          case intro assump_94 assump_95 =>
            cases assump_95
            case intro assump_98 assump_99 =>
              cases assump_99
              case intro assump_102 assump_103 =>
                apply Or.inl
                apply Or.inl
                intro assump_108
                intro assump_109
                cases assump_108
                case intro assump_112 assump_113 =>
                  apply False.elim assump_113


variable (p6 p2 p4 p7 p3 : Prop)
theorem file94_13380 : ((((((False → p3) ∧ (p7 → True)) → False) → (((False ∧ p6) → False) ∧ ((p3 ∨ p7) ∧ (p4 → p2)))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((False → p3) ∧ (p7 → True)) → False) → (((False ∧ p6) → False) ∧ ((p3 ∨ p7) ∧ (p4 → p2)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
    apply And.intro
    have assump_38 : ((False → p3) ∧ (p7 → True)) := by
      apply And.intro
      intro assump_14
      apply False.elim assump_14
      intro assump_17
      apply True.intro
    let assump_13 := assump_5 assump_38
    apply False.elim assump_13
    intro assump_21
    have assump_39 : ((False → p3) ∧ (p7 → True)) := by
      apply And.intro
      intro assump_27
      apply False.elim assump_27
      intro assump_30
      apply True.intro
    let assump_26 := assump_5 assump_39
    apply False.elim assump_26
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p4 p5 p6 p2 p0 : Prop)
theorem file94_14441 : (((((p2 ∨ True) → False) → ((p2 ∨ p5) ∨ (p5 ∧ p6))) ∧ (((p5 → p0) ∨ (p4 → True)) → False)) → ((((p4 ∧ p0) ∨ (p0 ∨ False)) ∧ ((True → p5) → (p5 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          have assump_49 : ((p5 → p0) ∨ (p4 → True)) := by
            apply Or.inl
            intro assump_22
            exact assump_8
          let assump_21 := assump_16 assump_49
          apply False.elim assump_21
    case inr assump_6 =>
      cases assump_6
      case inl assump_28 =>
        cases assump_1
        case intro assump_34 assump_35 =>
          have assump_50 : ((p5 → p0) ∨ (p4 → True)) := by
            apply Or.inl
            intro assump_41
            exact assump_28
          let assump_40 := assump_35 assump_50
          apply False.elim assump_40
      case inr assump_29 =>
        apply False.elim assump_29


variable (p3 p7 p5 p4 p1 : Prop)
theorem file94_15570 : (((((p3 ∨ True) ∧ (True ∨ True)) ∧ ((True ∨ p5) → False)) ∧ (((p5 ∧ p5) ∨ (p7 ∧ p1)) → False)) → ((((False → p7) ∨ (p5 ∧ True)) → ((p1 → p4) → False)) → (((p7 → False) → (p3 ∧ True)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_13
          case inl assump_18 =>
            have assump_68 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_27 := assump_11 assump_68
            apply False.elim assump_27
          case inr assump_19 =>
            have assump_69 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_38 := assump_11 assump_69
            apply False.elim assump_38
        case inr assump_15 =>
          cases assump_13
          case inl assump_44 =>
            have assump_70 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_53 := assump_11 assump_70
            apply False.elim assump_53
          case inr assump_45 =>
            have assump_71 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_64 := assump_11 assump_71
            apply False.elim assump_64


variable (p5 p4 p1 p7 p2 : Prop)
theorem file94_17084 : (((((p1 → False) → (p2 → p2)) ∨ ((p7 → False) ∧ (p4 → False))) → False) → ((((p5 → False) ∧ (p2 ∨ p7)) → False) ∧ (((p7 ∨ False) → False) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      have assump_52 : (((p1 → False) → (p2 → p2)) ∨ ((p7 → False) ∧ (p4 → False))) := by
        apply Or.inl
        intro assump_14
        intro assump_15
        exact assump_15
      let assump_13 := assump_1 assump_52
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_53 : (((p1 → False) → (p2 → p2)) ∨ ((p7 → False) ∧ (p4 → False))) := by
        apply Or.inl
        intro assump_28
        intro assump_29
        exact assump_29
      let assump_27 := assump_1 assump_53
      apply False.elim assump_27
  intro assump_37
  have assump_54 : (((p1 → False) → (p2 → p2)) ∨ ((p7 → False) ∧ (p4 → False))) := by
    apply Or.inl
    intro assump_43
    intro assump_44
    exact assump_44
  let assump_42 := assump_1 assump_54
  apply False.elim assump_42


variable (p1 p7 p6 p5 p3 p0 p2 : Prop)
theorem file94_18238 : ((((((p2 → False) → False) → ((p6 → False) → (p6 ∧ p1))) ∨ (((True ∧ p5) → False) → ((p7 ∧ p2) → (True → p5)))) ∧ ((((p0 ∨ p0) ∧ (True → False)) → ((False → p2) ∧ (p3 ∨ p2))) → False)) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case inl assump_17 =>
      have assump_83 : (((p0 ∨ p0) ∧ (True → False)) → ((False → p2) ∧ (p3 ∨ p2))) := by
        intro assump_24
        apply And.intro
        intro assump_25
        apply False.elim assump_25
        cases assump_24
        case intro assump_28 assump_29 =>
          cases assump_28
          case inl assump_30 =>
            have assump_84 : True := by
              apply True.intro
            let assump_36 := assump_29 assump_84
            apply False.elim assump_36
          case inr assump_31 =>
            have assump_85 : True := by
              apply True.intro
            let assump_44 := assump_29 assump_85
            apply False.elim assump_44
      let assump_23 := assump_16 assump_83
      apply False.elim assump_23
    case inr assump_18 =>
      have assump_86 : (((p0 ∨ p0) ∧ (True → False)) → ((False → p2) ∧ (p3 ∨ p2))) := by
        intro assump_56
        apply And.intro
        intro assump_57
        apply False.elim assump_57
        cases assump_56
        case intro assump_60 assump_61 =>
          cases assump_60
          case inl assump_62 =>
            have assump_87 : True := by
              apply True.intro
            let assump_68 := assump_61 assump_87
            apply False.elim assump_68
          case inr assump_63 =>
            have assump_88 : True := by
              apply True.intro
            let assump_76 := assump_61 assump_88
            apply False.elim assump_76
      let assump_55 := assump_16 assump_86
      apply False.elim assump_55


variable (p5 p4 p3 p7 p6 p0 : Prop)
theorem file94_20134 : (((((False → p5) → (True → p4)) → False) ∧ (((p4 → p6) → False) → ((p6 ∨ p7) ∨ (True ∧ p3)))) → ((((p0 ∧ False) → (p5 → True)) ∨ ((p5 → p4) ∧ (p4 ∧ p6))) ∨ (((p4 ∨ p6) ∧ (False → False)) ∨ ((False ∨ p7) → (p7 ∨ p6))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_8
    intro assump_9
    apply True.intro


variable (p1 p7 p2 p5 p4 p3 p6 p0 : Prop)
theorem file94_20586 : (((((True → False) ∧ (p7 → p6)) → ((False ∧ p0) ∧ (True → p3))) → False) → ((((p7 → False) ∨ (p7 → p6)) → False) ∨ (((False → p1) ∨ (p5 → False)) ∨ ((p4 ∨ p4) ∧ (p2 ∨ p0))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    have assump_95 : (((True → False) ∧ (p7 → p6)) → ((False ∧ p0) ∧ (True → p3))) := by
      intro assump_11
      apply And.intro
      apply And.intro
      cases assump_11
      case intro assump_12 assump_13 =>
        have assump_96 : True := by
          apply True.intro
        let assump_19 := assump_12 assump_96
        apply False.elim assump_19
      cases assump_11
      case intro assump_23 assump_24 =>
        have assump_97 : True := by
          apply True.intro
        let assump_30 := assump_23 assump_97
        apply False.elim assump_30
      intro assump_34
      cases assump_11
      case intro assump_37 assump_38 =>
        have assump_98 : True := by
          apply True.intro
        let assump_44 := assump_37 assump_98
        apply False.elim assump_44
    let assump_10 := assump_1 assump_95
    apply False.elim assump_10
  case inr assump_6 =>
    have assump_99 : (((True → False) ∧ (p7 → p6)) → ((False ∧ p0) ∧ (True → p3))) := by
      intro assump_55
      apply And.intro
      apply And.intro
      cases assump_55
      case intro assump_56 assump_57 =>
        have assump_100 : True := by
          apply True.intro
        let assump_63 := assump_56 assump_100
        apply False.elim assump_63
      cases assump_55
      case intro assump_67 assump_68 =>
        have assump_101 : True := by
          apply True.intro
        let assump_74 := assump_67 assump_101
        apply False.elim assump_74
      intro assump_78
      cases assump_55
      case intro assump_81 assump_82 =>
        have assump_102 : True := by
          apply True.intro
        let assump_88 := assump_81 assump_102
        apply False.elim assump_88
    let assump_54 := assump_1 assump_99
    apply False.elim assump_54


variable (p1 p5 p3 p7 p6 p4 p0 : Prop)
theorem file94_22674 : ((((((p1 ∧ True) ∨ (p0 ∨ p7)) → False) ∧ (((p0 → False) ∧ (True ∨ p1)) ∨ ((p3 → p5) → False))) ∧ ((((p0 → False) ∧ (True → p1)) ∧ ((p6 → p7) → False)) ∧ (((p6 ∧ p4) ∧ (True ∨ False)) ∧ ((p4 ∨ False) ∧ (p0 ∧ False))))) → False) := by
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
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  cases assump_19
                  case intro assump_30 assump_31 =>
                    cases assump_30
                    case intro assump_32 assump_33 =>
                      cases assump_32
                      case intro assump_34 assump_35 =>
                        cases assump_33
                        case inl assump_40 =>
                          cases assump_31
                          case intro assump_44 assump_45 =>
                            cases assump_44
                            case inl assump_46 =>
                              cases assump_45
                              case intro assump_50 assump_51 =>
                                apply False.elim assump_51
                            case inr assump_47 =>
                              apply False.elim assump_47
                        case inr assump_41 =>
                          apply False.elim assump_41
          case inr assump_15 =>
            cases assump_3
            case intro assump_62 assump_63 =>
              cases assump_62
              case intro assump_64 assump_65 =>
                cases assump_64
                case intro assump_66 assump_67 =>
                  cases assump_63
                  case intro assump_74 assump_75 =>
                    cases assump_74
                    case intro assump_76 assump_77 =>
                      cases assump_76
                      case intro assump_78 assump_79 =>
                        cases assump_77
                        case inl assump_84 =>
                          cases assump_75
                          case intro assump_88 assump_89 =>
                            cases assump_88
                            case inl assump_90 =>
                              cases assump_89
                              case intro assump_94 assump_95 =>
                                apply False.elim assump_95
                            case inr assump_91 =>
                              apply False.elim assump_91
                        case inr assump_85 =>
                          apply False.elim assump_85
      case inr assump_9 =>
        cases assump_3
        case intro assump_106 assump_107 =>
          cases assump_106
          case intro assump_108 assump_109 =>
            cases assump_108
            case intro assump_110 assump_111 =>
              cases assump_107
              case intro assump_118 assump_119 =>
                cases assump_118
                case intro assump_120 assump_121 =>
                  cases assump_120
                  case intro assump_122 assump_123 =>
                    cases assump_121
                    case inl assump_128 =>
                      cases assump_119
                      case intro assump_132 assump_133 =>
                        cases assump_132
                        case inl assump_134 =>
                          cases assump_133
                          case intro assump_138 assump_139 =>
                            apply False.elim assump_139
                        case inr assump_135 =>
                          apply False.elim assump_135
                    case inr assump_129 =>
                      apply False.elim assump_129


variable (p5 p1 p2 p6 p0 p4 : Prop)
theorem file94_26732 : ((((((p0 ∧ False) ∧ (p5 ∧ p0)) → ((p5 → p2) ∨ (p2 → p6))) ∨ (((p6 ∧ p0) → (p1 ∧ p1)) ∧ ((p4 → False) ∨ (p1 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p0 ∧ False) ∧ (p5 ∧ p0)) → ((p5 → p2) ∨ (p2 → p6))) ∨ (((p6 ∧ p0) → (p1 ∧ p1)) ∧ ((p4 → False) ∨ (p1 ∧ False)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p1 p6 p0 p2 p5 : Prop)
theorem file94_27340 : ((((((p5 ∨ p6) ∧ (p0 → False)) → False) → (((True ∨ True) ∨ (False ∧ p0)) → ((p2 ∨ p5) → (p1 → True)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p5 ∨ p6) ∧ (p0 → False)) → False) → (((True ∨ True) ∨ (False ∧ p0)) → ((p2 ∨ p5) → (p1 → True)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p3 p0 p4 p7 p2 p5 p1 p6 : Prop)
theorem file94_27840 : (((((p6 → False) → False) ∨ ((p2 → True) → False)) ∧ (((True → p3) → (True → p5)) → ((False → p1) ∨ (p0 ∨ p4)))) → ((((p6 → False) → (False → False)) ∧ ((p3 ∧ True) ∧ (p2 → p5))) ∨ (((p3 ∨ True) → False) → ((p6 ∨ p1) → (p7 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inr
      intro assump_14
      intro assump_15
      intro assump_16
      cases assump_15
      case inl assump_19 =>
        have assump_68 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_25 := assump_14 assump_68
        apply False.elim assump_25
      case inr assump_20 =>
        have assump_69 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_33 := assump_14 assump_69
        apply False.elim assump_33
    case inr assump_5 =>
      apply Or.inr
      intro assump_45
      intro assump_46
      intro assump_47
      cases assump_46
      case inl assump_50 =>
        have assump_70 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_56 := assump_45 assump_70
        apply False.elim assump_56
      case inr assump_51 =>
        have assump_71 : (p3 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_64 := assump_45 assump_71
        apply False.elim assump_64


variable (p5 p0 p2 p7 p1 p4 p3 : Prop)
theorem file94_29300 : ((((((False ∧ p3) ∧ (p3 → p1)) ∧ ((p3 ∨ p7) ∧ (p3 → False))) ∧ (((p3 ∨ p7) ∧ (p4 → p7)) → False)) ∧ ((((p5 ∨ False) ∧ (False ∨ p0)) → False) ∨ (((True → p5) → (p2 ∧ p0)) → False))) → False) := by
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


variable (p1 p3 p0 p7 p6 p4 : Prop)
theorem file94_29909 : ((((((True → False) ∧ (p7 → False)) → ((p6 → p1) ∨ (p1 → p1))) ∨ (((p3 ∨ p7) ∨ (p0 → False)) ∨ ((False → p4) → False))) → False) → False) := by
  intro assump_1
  have assump_24 : ((((True → False) ∧ (p7 → False)) → ((p6 → p1) ∨ (p1 → p1))) ∨ (((p3 ∨ p7) ∨ (p0 → False)) ∨ ((False → p4) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      have assump_25 : True := by
        apply True.intro
      let assump_17 := assump_6 assump_25
      apply False.elim assump_17
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p2 p1 p5 p3 p6 p7 p4 p0 : Prop)
theorem file94_30610 : (((((False ∧ p2) ∧ (p3 ∨ p5)) ∧ ((p3 ∧ p0) ∨ (p3 → True))) → (((p3 ∨ p4) → False) → ((p2 ∧ False) ∧ (p4 ∨ p6)))) ∨ ((((False ∧ p1) ∧ (False → p7)) ∧ ((p3 ∧ p6) → (p5 ∧ p7))) ∧ (((p7 ∨ p1) ∨ (p2 ∨ p4)) ∧ ((p3 → False) ∧ (p5 ∨ p6))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
  cases assump_1
  case intro assump_15 assump_16 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        apply False.elim assump_19
  cases assump_1
  case intro assump_25 assump_26 =>
    cases assump_25
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        apply False.elim assump_29


variable (p3 p5 p4 p7 : Prop)
theorem file94_31604 : ((((((p4 → False) → (p5 → p5)) → False) → (((p7 → p7) ∨ (False ∨ p7)) ∧ ((p7 ∧ True) → (p3 → False)))) → False) → False) := by
  intro assump_1
  have assump_36 : ((((p4 → False) → (p5 → p5)) → False) → (((p7 → p7) ∨ (False ∨ p7)) ∧ ((p7 ∧ True) → (p3 → False)))) := by
    intro assump_5
    apply And.intro
    apply Or.inl
    intro assump_8
    exact assump_8
    intro assump_11
    intro assump_12
    cases assump_11
    case intro assump_15 assump_16 =>
      have assump_37 : ((p4 → False) → (p5 → p5)) := by
        intro assump_24
        intro assump_25
        exact assump_25
      let assump_23 := assump_5 assump_37
      apply False.elim assump_23
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p3 p6 p7 p5 p0 p4 p2 : Prop)
theorem file94_32397 : (((((p3 ∧ False) ∧ (p5 ∨ p4)) ∨ ((p6 ∨ p0) → (p7 ∧ p2))) ∧ (((False → p5) ∨ (p2 ∧ True)) → ((False → p6) → False))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
    case inr assump_11 =>
      have assump_35 : ((False → p5) ∨ (p2 ∧ True)) := by
        apply Or.inl
        intro assump_25
        apply False.elim assump_25
      let assump_24 := assump_9 assump_35
      have assump_36 : (False → p6) := by
        intro assump_29
        apply False.elim assump_29
      let assump_28 := assump_24 assump_36
      apply False.elim assump_28


variable (p4 p3 p6 p5 p7 : Prop)
theorem file94_33246 : ((((((p6 ∧ p6) → False) → ((False ∧ p6) → (p4 ∧ p7))) → (((p4 ∧ True) → (True ∨ p3)) ∨ ((p7 → p5) → False))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p6 ∧ p6) → False) → ((False ∧ p6) → (p4 ∧ p7))) → (((p4 ∧ True) → (True ∨ p3)) ∨ ((p7 → p5) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p4 p5 p6 p1 p2 p0 : Prop)
theorem file94_33809 : ((((((False ∧ p5) → (p7 ∨ True)) ∨ ((p2 ∨ p6) → False)) → (((p4 ∧ False) ∧ (True → False)) ∨ ((p6 ∨ True) → False))) ∨ ((((p5 ∨ p1) → False) → ((p0 ∧ p2) → False)) ∧ (((p6 → True) → False) ∧ ((p0 → False) ∨ (p6 → p4))))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_55 : (((False ∧ p5) → (p7 ∨ True)) ∨ ((p2 ∨ p6) → False)) := by
      apply Or.inl
      intro assump_7
      cases assump_7
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
    let assump_6 := assump_2 assump_55
    cases assump_6
    case inl assump_13 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          apply False.elim assump_18
    case inr assump_14 =>
      have assump_56 : (p6 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_25 := assump_14 assump_56
      apply False.elim assump_25
  case inr assump_3 =>
    cases assump_3
    case intro assump_29 assump_30 =>
      cases assump_30
      case intro assump_33 assump_34 =>
        cases assump_34
        case inl assump_37 =>
          have assump_57 : (p6 → True) := by
            intro assump_43
            apply True.intro
          let assump_42 := assump_33 assump_57
          apply False.elim assump_42
        case inr assump_38 =>
          have assump_58 : (p6 → True) := by
            intro assump_51
            apply True.intro
          let assump_50 := assump_33 assump_58
          apply False.elim assump_50


variable (p0 p2 p5 p1 p6 p4 : Prop)
theorem file94_35411 : ((((((False → True) → False) → ((p1 → False) → (p2 ∨ p0))) → (((p6 ∧ True) → False) ∧ ((p1 → False) → (p5 ∧ p0)))) ∧ ((((p1 ∧ False) → (p0 ∨ p4)) ∧ ((False → False) ∨ (p4 → False))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_26 : (((p1 ∧ False) → (p0 ∨ p4)) ∧ ((False → False) ∨ (p4 → False))) := by
      apply And.intro
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
      apply Or.inl
      intro assump_20
      apply False.elim assump_20
    let assump_12 := assump_7 assump_26
    apply False.elim assump_12


variable (p0 p3 p6 : Prop)
theorem file94_36114 : ((((((True ∨ True) → (p6 → True)) → False) → (((p0 → False) ∨ (p3 → False)) → False)) → False) → False) := by
  intro assump_5
  have assump_36 : ((((True ∨ True) → (p6 → True)) → False) → (((p0 → False) ∨ (p3 → False)) → False)) := by
    intro assump_9
    intro assump_10
    cases assump_10
    case inl assump_11 =>
      have assump_37 : ((True ∨ True) → (p6 → True)) := by
        intro assump_18
        intro assump_19
        apply True.intro
      let assump_17 := assump_9 assump_37
      apply False.elim assump_17
    case inr assump_12 =>
      have assump_38 : ((True ∨ True) → (p6 → True)) := by
        intro assump_28
        intro assump_29
        apply True.intro
      let assump_27 := assump_9 assump_38
      apply False.elim assump_27
  let assump_8 := assump_5 assump_36
  apply False.elim assump_8


variable (p2 p7 p0 p3 p5 : Prop)
theorem file94_36997 : (((((False → False) ∧ (False ∨ p2)) ∧ ((p7 ∨ p0) ∧ (p3 ∨ p2))) ∧ (((p3 → False) → False) ∧ ((p7 ∧ p5) ∧ (False ∨ p0)))) ∨ ((((p0 ∨ True) → False) ∧ ((False ∧ True) ∧ (p5 ∧ p7))) → False)) := by
  apply Or.inr
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_11


variable (p0 p1 p7 p5 p4 : Prop)
theorem file94_37483 : ((((((p7 → False) → False) ∨ ((p5 ∧ p0) → (p7 → p7))) → (((p0 → True) → (True ∨ p4)) ∨ ((p1 ∨ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p7 → False) → False) ∨ ((p5 ∧ p0) → (p7 → p7))) → (((p0 → True) → (True ∨ p4)) ∨ ((p1 ∨ p1) → False))) := by
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


variable (p4 p3 p6 : Prop)
theorem file94_38135 : (((((False → False) → False) → False) → False) → ((((p3 → p4) → False) ∧ ((p6 ∨ True) ∨ (p3 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        have assump_65 : (((False → False) → False) → False) := by
          intro assump_16
          have assump_66 : (False → False) := by
            intro assump_20
            apply False.elim assump_20
          let assump_19 := assump_16 assump_66
          apply False.elim assump_19
        let assump_15 := assump_1 assump_65
        apply False.elim assump_15
      case inr assump_10 =>
        have assump_67 : (((False → False) → False) → False) := by
          intro assump_34
          have assump_68 : (False → False) := by
            intro assump_38
            apply False.elim assump_38
          let assump_37 := assump_34 assump_68
          apply False.elim assump_37
        let assump_33 := assump_1 assump_67
        apply False.elim assump_33
    case inr assump_8 =>
      have assump_69 : (((False → False) → False) → False) := by
        intro assump_52
        have assump_70 : (False → False) := by
          intro assump_56
          apply False.elim assump_56
        let assump_55 := assump_52 assump_70
        apply False.elim assump_55
      let assump_51 := assump_1 assump_69
      apply False.elim assump_51


variable (p0 p4 p5 p6 : Prop)
theorem file94_39636 : ((((((False ∧ p6) ∧ (p0 → False)) → ((p6 ∧ True) ∨ (p5 → False))) ∨ (((p4 ∧ False) ∨ (True → False)) ∨ ((p4 ∧ True) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((False ∧ p6) ∧ (p0 → False)) → ((p6 ∧ True) ∨ (p5 → False))) ∨ (((p4 ∧ False) ∨ (True → False)) ∨ ((p4 ∧ True) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p6 p5 p4 p7 p2 : Prop)
theorem file94_40263 : (((((True → p3) ∧ (p3 → p6)) ∧ ((p2 ∧ False) → (p6 → p4))) ∨ (((p7 ∧ p2) → False) ∨ ((p5 ∧ p2) ∨ (True → False)))) → ((((p3 → p3) ∨ (p4 ∧ p7)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        have assump_63 : ((p3 → p3) ∨ (p4 ∧ p7)) := by
          apply Or.inl
          intro assump_22
          exact assump_22
        let assump_21 := assump_2 assump_63
        apply False.elim assump_21
  case inr assump_6 =>
    cases assump_6
    case inl assump_28 =>
      have assump_64 : ((p3 → p3) ∨ (p4 ∧ p7)) := by
        apply Or.inl
        intro assump_34
        exact assump_34
      let assump_33 := assump_2 assump_64
      apply False.elim assump_33
    case inr assump_29 =>
      cases assump_29
      case inl assump_40 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          have assump_65 : ((p3 → p3) ∨ (p4 ∧ p7)) := by
            apply Or.inl
            intro assump_51
            exact assump_51
          let assump_50 := assump_2 assump_65
          apply False.elim assump_50
      case inr assump_41 =>
        have assump_66 : True := by
          apply True.intro
        let assump_59 := assump_41 assump_66
        apply False.elim assump_59


variable (p5 p3 p2 p4 p7 p0 p6 : Prop)
theorem file94_41691 : (((((p4 → False) ∧ (False → False)) → ((p4 ∧ p5) → False)) ∨ (((True ∨ p4) → (False ∨ p5)) → False)) ∨ ((((p4 → False) → False) ∧ ((False → False) → False)) → (((p3 ∧ p4) ∧ (p6 ∧ p0)) ∨ ((p2 ∧ p3) → (p0 → p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      have assump_20 : p4 := by
        exact assump_3
      let assump_16 := assump_9 assump_20
      apply False.elim assump_16


variable (p5 p1 p4 p2 : Prop)
theorem file94_42265 : (((((False → False) ∧ (p5 ∨ True)) ∧ ((p5 → True) → False)) ∧ (((p1 → True) ∧ (p4 ∨ True)) ∨ ((p2 ∧ p5) → False))) → False) := by
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        cases assump_21
        case inl assump_24 =>
          cases assump_17
          case inl assump_30 =>
            cases assump_30
            case intro assump_32 assump_33 =>
              cases assump_33
              case inl assump_36 =>
                have assump_100 : (p5 → True) := by
                  intro assump_43
                  apply True.intro
                let assump_42 := assump_19 assump_100
                apply False.elim assump_42
              case inr assump_37 =>
                have assump_101 : (p5 → True) := by
                  intro assump_51
                  apply True.intro
                let assump_50 := assump_19 assump_101
                apply False.elim assump_50
          case inr assump_31 =>
            have assump_102 : (p5 → True) := by
              intro assump_59
              apply True.intro
            let assump_58 := assump_19 assump_102
            apply False.elim assump_58
        case inr assump_25 =>
          cases assump_17
          case inl assump_67 =>
            cases assump_67
            case intro assump_69 assump_70 =>
              cases assump_70
              case inl assump_73 =>
                have assump_103 : (p5 → True) := by
                  intro assump_80
                  apply True.intro
                let assump_79 := assump_19 assump_103
                apply False.elim assump_79
              case inr assump_74 =>
                have assump_104 : (p5 → True) := by
                  intro assump_88
                  apply True.intro
                let assump_87 := assump_19 assump_104
                apply False.elim assump_87
          case inr assump_68 =>
            have assump_105 : (p5 → True) := by
              intro assump_96
              apply True.intro
            let assump_95 := assump_19 assump_105
            apply False.elim assump_95


variable (p0 p6 p1 p4 p3 p5 p2 p7 : Prop)
theorem file94_44537 : (((((p6 → p1) ∧ (p4 ∨ p7)) → False) ∨ (((p6 ∨ p0) → (True → p5)) ∨ ((p0 → p2) ∨ (p7 → False)))) → ((((p2 ∧ p7) ∨ (p5 → p2)) ∧ ((p3 ∧ p3) ∨ (p1 → False))) → (((False → p1) ∨ (True ∧ True)) ∨ ((p0 ∨ False) ∧ (p7 → p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_4
        case inl assump_13 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_1
            case inl assump_21 =>
              apply Or.inl
              apply Or.inl
              intro assump_25
              apply False.elim assump_25
            case inr assump_22 =>
              cases assump_22
              case inl assump_28 =>
                apply Or.inl
                apply Or.inl
                intro assump_32
                apply False.elim assump_32
              case inr assump_29 =>
                cases assump_29
                case inl assump_35 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_39
                  apply False.elim assump_39
                case inr assump_36 =>
                  apply Or.inl
                  apply Or.inl
                  intro assump_44
                  apply False.elim assump_44
        case inr assump_14 =>
          cases assump_1
          case inl assump_49 =>
            apply Or.inl
            apply Or.inl
            intro assump_53
            apply False.elim assump_53
          case inr assump_50 =>
            cases assump_50
            case inl assump_56 =>
              apply Or.inl
              apply Or.inl
              intro assump_60
              apply False.elim assump_60
            case inr assump_57 =>
              cases assump_57
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
    case inr assump_6 =>
      cases assump_4
      case inl assump_77 =>
        cases assump_77
        case intro assump_79 assump_80 =>
          cases assump_1
          case inl assump_85 =>
            apply Or.inl
            apply Or.inl
            intro assump_89
            apply False.elim assump_89
          case inr assump_86 =>
            cases assump_86
            case inl assump_92 =>
              apply Or.inl
              apply Or.inl
              intro assump_96
              apply False.elim assump_96
            case inr assump_93 =>
              cases assump_93
              case inl assump_99 =>
                apply Or.inl
                apply Or.inl
                intro assump_103
                apply False.elim assump_103
              case inr assump_100 =>
                apply Or.inl
                apply Or.inl
                intro assump_108
                apply False.elim assump_108
      case inr assump_78 =>
        cases assump_1
        case inl assump_113 =>
          apply Or.inl
          apply Or.inl
          intro assump_117
          apply False.elim assump_117
        case inr assump_114 =>
          cases assump_114
          case inl assump_120 =>
            apply Or.inl
            apply Or.inl
            intro assump_124
            apply False.elim assump_124
          case inr assump_121 =>
            cases assump_121
            case inl assump_127 =>
              apply Or.inl
              apply Or.inl
              intro assump_131
              apply False.elim assump_131
            case inr assump_128 =>
              apply Or.inl
              apply Or.inl
              intro assump_136
              apply False.elim assump_136


variable (p7 p6 : Prop)
theorem file94_48521 : (((((True ∧ p7) ∧ (False ∨ False)) → ((p6 → False) → False)) → False) → False) := by
  intro assump_1
  have assump_26 : (((True ∧ p7) ∧ (False ∨ False)) → ((p6 → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case inl assump_17 =>
          apply False.elim assump_17
        case inr assump_18 =>
          apply False.elim assump_18
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p7 p1 p5 p6 p0 : Prop)
theorem file94_49142 : (((((p7 → False) → (p1 ∨ True)) → ((p6 ∨ p0) → (True ∨ p6))) → False) → ((((True ∧ True) ∨ (p1 ∧ p7)) → False) → (((True → False) → False) ∧ ((p0 → False) ∧ (p5 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  have assump_72 : (((p7 → False) → (p1 ∨ True)) → ((p6 ∨ p0) → (True ∨ p6))) := by
    intro assump_11
    intro assump_12
    cases assump_12
    case inl assump_13 =>
      apply Or.inl
      apply True.intro
    case inr assump_14 =>
      apply Or.inl
      apply True.intro
  let assump_10 := assump_1 assump_72
  apply False.elim assump_10
  apply And.intro
  intro assump_26
  have assump_73 : (((p7 → False) → (p1 ∨ True)) → ((p6 ∨ p0) → (True ∨ p6))) := by
    intro assump_34
    intro assump_35
    cases assump_35
    case inl assump_36 =>
      apply Or.inl
      apply True.intro
    case inr assump_37 =>
      apply Or.inl
      apply True.intro
  let assump_33 := assump_1 assump_73
  apply False.elim assump_33
  intro assump_49
  have assump_74 : (((p7 → False) → (p1 ∨ True)) → ((p6 ∨ p0) → (True ∨ p6))) := by
    intro assump_57
    intro assump_58
    cases assump_58
    case inl assump_59 =>
      apply Or.inl
      apply True.intro
    case inr assump_60 =>
      apply Or.inl
      apply True.intro
  let assump_56 := assump_1 assump_74
  apply False.elim assump_56


variable (p6 p3 p4 p1 p5 p7 : Prop)
theorem file94_50546 : (((((False → False) → False) → ((p5 ∧ False) → False)) → (((p5 ∨ False) ∧ (False ∧ True)) → ((False → False) ∧ (p1 → False)))) ∨ ((((p6 → False) ∨ (p6 ∨ p3)) ∨ ((p7 → False) ∧ (p7 → p4))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  apply False.elim assump_3
  intro assump_6
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      cases assump_10
      case intro assump_15 assump_16 =>
        apply False.elim assump_15
    case inr assump_12 =>
      apply False.elim assump_12


variable (p3 p1 p7 : Prop)
theorem file94_51183 : (((((False → p3) → False) → ((p7 ∧ p1) ∨ (False ∨ p7))) → False) → False) := by
  intro assump_1
  have assump_18 : (((False → p3) → False) → ((p7 ∧ p1) ∨ (False ∨ p7))) := by
    intro assump_5
    have assump_19 : (False → p3) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p2 p6 p5 p3 p4 p7 : Prop)
theorem file94_51668 : (((((p3 ∨ True) → False) ∨ ((p0 ∧ p7) ∨ (p0 ∧ False))) → False) → ((((False → False) ∨ (p5 → p6)) ∨ ((p7 ∧ p3) ∧ (p2 → False))) ∨ (((p0 → p4) ∧ (p5 ∨ p4)) ∨ ((True → False) → (True ∧ p2))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p7 p5 p4 : Prop)
theorem file94_52023 : (((((p5 → True) ∧ (p5 ∧ False)) ∧ ((False ∧ p4) → (p7 → False))) → False) ∧ ((((False ∨ p4) ∨ (False ∨ True)) → False) → False)) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  intro assump_14
  have assump_21 : ((False ∨ p4) ∨ (False ∨ True)) := by
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_17 := assump_14 assump_21
  apply False.elim assump_17


variable (p1 p4 p6 p7 p5 : Prop)
theorem file94_52647 : ((((((p7 → p4) → False) → ((p4 → False) → False)) → False) ∧ ((((p7 ∨ True) ∨ (p6 → p1)) ∨ ((p5 → p4) → False)) → (((p1 → p6) ∧ (True → False)) ∧ ((p1 → p5) ∧ (p6 → p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((p7 ∨ True) ∨ (p6 → p1)) ∨ ((p5 → p4) → False)) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_8 := assump_3 assump_16
    let assump_9 := And.left assump_8
    let assump_10 := And.right assump_9
    have assump_17 : True := by
      apply True.intro
    let assump_12 := assump_10 assump_17
    apply False.elim assump_12


variable (p4 p7 p2 p3 p0 p1 p5 p6 : Prop)
theorem file94_53370 : (((((p3 ∨ True) → False) ∧ ((p3 ∧ p4) → (True ∨ p4))) → (((p5 ∨ p0) ∨ (p2 → False)) ∨ ((p7 ∨ p2) → False))) ∧ ((((False ∧ p6) → False) ∨ ((p3 → p4) ∧ (p4 → False))) ∨ (((True → False) → (p3 → p0)) ∧ ((p0 → False) → (p4 → p1))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inr
    intro assump_8
    have assump_22 : (p3 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_13 := assump_2 assump_22
    apply False.elim assump_13
  apply Or.inl
  apply Or.inl
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    apply False.elim assump_18


variable (p5 p3 p7 p4 p1 : Prop)
theorem file94_54086 : (((((False → p3) → (False ∨ p5)) ∧ ((p4 → False) → False)) ∨ (((p4 → p7) ∨ (p1 → False)) → False)) → ((((p4 → False) → (p1 → False)) ∨ ((p7 → p1) ∧ (p4 ∨ False))) ∨ (((p5 → False) ∨ (p7 ∧ p1)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply Or.inl
      intro assump_10
      intro assump_11
      have assump_52 : (p4 → False) := by
        intro assump_19
        have assump_53 : p4 := by
          exact assump_19
        let assump_23 := assump_10 assump_53
        apply False.elim assump_23
      let assump_18 := assump_5 assump_52
      apply False.elim assump_18
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_32
    intro assump_33
    have assump_54 : ((p4 → p7) ∨ (p1 → False)) := by
      apply Or.inl
      intro assump_41
      have assump_55 : p4 := by
        exact assump_41
      let assump_45 := assump_32 assump_55
      apply False.elim assump_45
    let assump_40 := assump_3 assump_54
    apply False.elim assump_40


variable (p2 p3 p0 p5 p6 p4 p1 : Prop)
theorem file94_55229 : (((((True ∧ False) → (False → p5)) ∨ ((p2 ∧ p3) → (p2 → False))) ∨ (((p5 → p0) ∨ (p6 ∧ False)) → ((p5 ∨ False) ∧ (p3 → False)))) → ((((p4 → p4) → False) → ((p3 ∨ p2) ∧ (p2 ∧ p2))) ∨ (((p5 → p3) → (p2 → False)) → ((p2 ∨ p1) ∧ (p2 ∧ p6))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_8
      apply And.intro
      have assump_96 : (p4 → p4) := by
        intro assump_12
        exact assump_12
      let assump_11 := assump_8 assump_96
      apply False.elim assump_11
      apply And.intro
      have assump_97 : (p4 → p4) := by
        intro assump_21
        exact assump_21
      let assump_20 := assump_8 assump_97
      apply False.elim assump_20
      have assump_98 : (p4 → p4) := by
        intro assump_30
        exact assump_30
      let assump_29 := assump_8 assump_98
      apply False.elim assump_29
    case inr assump_5 =>
      apply Or.inl
      intro assump_38
      apply And.intro
      have assump_99 : (p4 → p4) := by
        intro assump_42
        exact assump_42
      let assump_41 := assump_38 assump_99
      apply False.elim assump_41
      apply And.intro
      have assump_100 : (p4 → p4) := by
        intro assump_51
        exact assump_51
      let assump_50 := assump_38 assump_100
      apply False.elim assump_50
      have assump_101 : (p4 → p4) := by
        intro assump_60
        exact assump_60
      let assump_59 := assump_38 assump_101
      apply False.elim assump_59
  case inr assump_3 =>
    apply Or.inl
    intro assump_68
    apply And.intro
    have assump_102 : (p4 → p4) := by
      intro assump_72
      exact assump_72
    let assump_71 := assump_68 assump_102
    apply False.elim assump_71
    apply And.intro
    have assump_103 : (p4 → p4) := by
      intro assump_81
      exact assump_81
    let assump_80 := assump_68 assump_103
    apply False.elim assump_80
    have assump_104 : (p4 → p4) := by
      intro assump_90
      exact assump_90
    let assump_89 := assump_68 assump_104
    apply False.elim assump_89


variable (p5 p2 p0 p7 p6 : Prop)
theorem file94_57370 : (((((p0 ∨ p7) ∨ (p0 → p6)) → False) ∧ (((p5 → False) → (True ∨ p7)) → ((p2 ∧ False) → False))) → False) := by
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    have assump_44 : ((p0 ∨ p7) ∨ (p0 → p6)) := by
      apply Or.inr
      intro assump_28
      have assump_45 : ((p0 ∨ p7) ∨ (p0 → p6)) := by
        apply Or.inl
        apply Or.inl
        exact assump_28
      let assump_37 := assump_16 assump_45
      apply False.elim assump_37
    let assump_27 := assump_16 assump_44
    apply False.elim assump_27


variable (p2 p5 p1 p7 p0 p4 p6 p3 : Prop)
theorem file94_57977 : ((((((p2 ∧ False) → (p6 ∨ True)) ∧ ((p0 → False) → (p7 → True))) → False) ∧ ((((p6 ∨ p2) ∧ (p6 ∨ p2)) ∧ ((p5 → p3) ∧ (p2 → p1))) → (((p4 ∧ p6) → (p7 → p5)) → False))) → False) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    have assump_31 : (((p2 ∧ False) → (p6 ∨ True)) ∧ ((p0 → False) → (p7 → True))) := by
      apply And.intro
      intro assump_19
      cases assump_19
      case intro assump_20 assump_21 =>
        apply False.elim assump_21
      intro assump_26
      intro assump_27
      apply True.intro
    let assump_18 := assump_11 assump_31
    apply False.elim assump_18


variable (p7 p6 p5 p0 p3 p1 : Prop)
theorem file94_58660 : (((((False → p6) ∨ (True ∨ p0)) ∧ ((p0 → p0) → False)) → False) ∨ ((((p3 → p1) ∧ (p1 → False)) → False) → (((p5 ∨ p3) ∧ (True → False)) → ((False → False) ∨ (p3 → p7))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_41 : (p0 → p0) := by
        intro assump_11
        exact assump_11
      let assump_10 := assump_3 assump_41
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_17 =>
        have assump_42 : (p0 → p0) := by
          intro assump_24
          exact assump_24
        let assump_23 := assump_3 assump_42
        apply False.elim assump_23
      case inr assump_18 =>
        have assump_43 : (p0 → p0) := by
          intro assump_35
          exact assump_35
        let assump_34 := assump_3 assump_43
        apply False.elim assump_34


variable (p7 p6 p3 p2 p0 p1 p4 : Prop)
theorem file94_59635 : ((((((p0 → p0) ∧ (p1 ∧ p2)) ∧ ((p3 → p7) → False)) → (((p3 ∨ p1) → (False ∨ p4)) → ((p6 → p2) ∨ (p1 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p0 → p0) ∧ (p1 ∧ p2)) ∧ ((p3 → p7) → False)) → (((p3 ∨ p1) → (False ∨ p4)) → ((p6 → p2) ∨ (p1 ∨ False)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          apply Or.inl
          intro assump_23
          exact assump_16
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p1 p4 : Prop)
theorem file94_60332 : ((((((p4 ∨ True) ∨ (p1 ∨ False)) → False) → False) → False) → False) := by
  intro assump_7
  have assump_21 : ((((p4 ∨ True) ∨ (p1 ∨ False)) → False) → False) := by
    intro assump_11
    have assump_22 : ((p4 ∨ True) ∨ (p1 ∨ False)) := by
      apply Or.inl
      apply Or.inr
      apply True.intro
    let assump_14 := assump_11 assump_22
    apply False.elim assump_14
  let assump_10 := assump_7 assump_21
  apply False.elim assump_10


variable (p2 p5 p1 p0 p7 p4 p3 p6 : Prop)
theorem file94_60840 : (((((False ∧ p5) → False) ∧ ((p1 → p4) ∨ (p4 → p4))) ∧ (((p2 → p2) → False) ∧ ((p1 ∧ True) → False))) → ((((False → False) ∧ (True → False)) → ((p7 → False) ∧ (p2 → False))) ∧ (((p6 ∧ p7) → (True ∧ p3)) ∧ ((p6 → p0) → False)))) := by
  intro assump_5
  apply And.intro
  intro assump_6
  apply And.intro
  intro assump_7
  cases assump_6
  case intro assump_10 assump_11 =>
    cases assump_5
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_19
        case inl assump_22 =>
          cases assump_17
          case intro assump_26 assump_27 =>
            have assump_195 : (p2 → p2) := by
              intro assump_34
              exact assump_34
            let assump_33 := assump_26 assump_195
            apply False.elim assump_33
        case inr assump_23 =>
          cases assump_17
          case intro assump_42 assump_43 =>
            have assump_196 : (p2 → p2) := by
              intro assump_50
              exact assump_50
            let assump_49 := assump_42 assump_196
            apply False.elim assump_49
  intro assump_56
  cases assump_6
  case intro assump_59 assump_60 =>
    cases assump_5
    case intro assump_65 assump_66 =>
      cases assump_65
      case intro assump_67 assump_68 =>
        cases assump_68
        case inl assump_71 =>
          cases assump_66
          case intro assump_75 assump_76 =>
            have assump_197 : (p2 → p2) := by
              intro assump_83
              exact assump_83
            let assump_82 := assump_75 assump_197
            apply False.elim assump_82
        case inr assump_72 =>
          cases assump_66
          case intro assump_91 assump_92 =>
            have assump_198 : (p2 → p2) := by
              intro assump_99
              exact assump_99
            let assump_98 := assump_91 assump_198
            apply False.elim assump_98
  apply And.intro
  intro assump_105
  apply And.intro
  apply True.intro
  cases assump_105
  case intro assump_106 assump_107 =>
    cases assump_5
    case intro assump_112 assump_113 =>
      cases assump_112
      case intro assump_114 assump_115 =>
        cases assump_115
        case inl assump_118 =>
          cases assump_113
          case intro assump_122 assump_123 =>
            have assump_199 : (p2 → p2) := by
              intro assump_130
              exact assump_130
            let assump_129 := assump_122 assump_199
            apply False.elim assump_129
        case inr assump_119 =>
          cases assump_113
          case intro assump_138 assump_139 =>
            have assump_200 : (p2 → p2) := by
              intro assump_146
              exact assump_146
            let assump_145 := assump_138 assump_200
            apply False.elim assump_145
  intro assump_152
  cases assump_5
  case intro assump_155 assump_156 =>
    cases assump_155
    case intro assump_157 assump_158 =>
      cases assump_158
      case inl assump_161 =>
        cases assump_156
        case intro assump_165 assump_166 =>
          have assump_201 : (p2 → p2) := by
            intro assump_173
            exact assump_173
          let assump_172 := assump_165 assump_201
          apply False.elim assump_172
      case inr assump_162 =>
        cases assump_156
        case intro assump_181 assump_182 =>
          have assump_202 : (p2 → p2) := by
            intro assump_189
            exact assump_189
          let assump_188 := assump_181 assump_202
          apply False.elim assump_188


variable (p0 p2 p3 p5 : Prop)
theorem file94_64427 : (((((p0 → p0) ∧ (False → False)) → False) → False) ∧ ((((True → False) ∧ (p5 ∧ True)) ∨ ((p2 ∨ p3) ∧ (True → False))) → False)) := by
  apply And.intro
  intro assump_1
  have assump_52 : ((p0 → p0) ∧ (False → False)) := by
    apply And.intro
    intro assump_5
    exact assump_5
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_52
  apply False.elim assump_4
  intro assump_14
  cases assump_14
  case inl assump_15 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_18
      case intro assump_21 assump_22 =>
        have assump_53 : True := by
          apply True.intro
        let assump_28 := assump_17 assump_53
        apply False.elim assump_28
  case inr assump_16 =>
    cases assump_16
    case intro assump_32 assump_33 =>
      cases assump_32
      case inl assump_34 =>
        have assump_54 : True := by
          apply True.intro
        let assump_40 := assump_33 assump_54
        apply False.elim assump_40
      case inr assump_35 =>
        have assump_55 : True := by
          apply True.intro
        let assump_48 := assump_33 assump_55
        apply False.elim assump_48


variable (p1 p7 p6 p3 p2 p0 p5 : Prop)
theorem file94_65655 : ((((((p2 → False) → (p2 ∧ p6)) ∨ ((p2 → p7) ∨ (p1 → p5))) → False) ∧ ((((p0 ∧ p3) ∨ (p3 → p0)) → ((p5 ∧ p5) → (p1 ∨ True))) → False)) → False) := by
  intro assump_25
  cases assump_25
  case intro assump_26 assump_27 =>
    have assump_54 : (((p0 ∧ p3) ∨ (p3 → p0)) → ((p5 ∧ p5) → (p1 ∨ True))) := by
      intro assump_33
      intro assump_34
      cases assump_34
      case intro assump_35 assump_36 =>
        cases assump_33
        case inl assump_41 =>
          cases assump_41
          case intro assump_43 assump_44 =>
            apply Or.inr
            apply True.intro
        case inr assump_42 =>
          apply Or.inr
          apply True.intro
    let assump_32 := assump_27 assump_54
    apply False.elim assump_32


variable (p3 p0 p6 p7 : Prop)
theorem file94_66447 : ((((((p3 → False) ∨ (p0 ∨ True)) → ((p3 ∧ p6) → (p6 ∨ p7))) ∨ (((p0 ∧ True) ∨ (p0 ∨ False)) → False)) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p3 → False) ∨ (p0 ∨ True)) → ((p3 ∧ p6) → (p6 ∨ p7))) ∨ (((p0 ∧ True) ∨ (p0 ∨ False)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case inl assump_13 =>
        apply Or.inl
        exact assump_8
      case inr assump_14 =>
        cases assump_14
        case inl assump_17 =>
          apply Or.inl
          exact assump_8
        case inr assump_18 =>
          apply Or.inl
          exact assump_8
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p4 p6 p5 p0 p1 : Prop)
theorem file94_67248 : ((((((False → False) → (p0 ∧ p6)) → False) → False) ∧ ((((False → True) ∨ (p4 ∨ p6)) ∨ ((p1 → False) → (p4 ∧ p5))) → False)) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    have assump_23 : (((False → True) ∨ (p4 ∨ p6)) ∨ ((p1 → False) → (p4 ∧ p5))) := by
      apply Or.inl
      apply Or.inl
      intro assump_19
      apply True.intro
    let assump_18 := assump_13 assump_23
    apply False.elim assump_18


variable (p4 p5 p2 p6 p1 p7 p0 : Prop)
theorem file94_67765 : ((((((p7 ∨ p0) ∨ (p2 ∨ p1)) ∨ ((p6 ∨ p4) ∨ (p5 → True))) ∨ (((p0 ∧ p6) → False) ∧ ((p0 → True) → (True ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_9 : ((((p7 ∨ p0) ∨ (p2 ∨ p1)) ∨ ((p6 ∨ p4) ∨ (p5 → True))) ∨ (((p0 ∧ p6) → False) ∧ ((p0 → True) → (True ∧ True)))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p5 p1 p2 p6 p7 p0 p4 : Prop)
theorem file94_68274 : (((((p2 ∨ p5) ∧ (p2 → False)) ∨ ((p7 ∨ p1) ∧ (p4 ∧ False))) → (((p6 ∧ p1) ∨ (p6 → p0)) → ((p7 ∧ p0) ∧ (p0 ∧ p2)))) → ((((False → p1) → False) → False) ∨ (((False → p5) ∨ (p0 ∨ p4)) → ((p7 ∧ False) → False)))) := by
  intro assump_5
  apply Or.inl
  intro assump_8
  have assump_18 : (False → p1) := by
    intro assump_12
    apply False.elim assump_12
  let assump_11 := assump_8 assump_18
  apply False.elim assump_11


variable (p6 p3 p4 p0 p5 p1 p2 : Prop)
theorem file94_68757 : (((((False → p3) → False) ∧ ((p1 ∨ p6) ∧ (p0 → p2))) ∧ (((False → False) → False) ∧ ((p2 → True) → False))) → ((((p1 → False) → False) ∧ ((True → False) ∨ (p6 ∧ p1))) ∨ (((p2 ∨ p0) ∨ (p5 → False)) → ((p0 ∨ p4) ∧ (p2 → p0))))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_7
          case intro assump_20 assump_21 =>
            apply Or.inl
            apply And.intro
            intro assump_26
            have assump_68 : p1 := by
              exact assump_14
            let assump_29 := assump_26 assump_68
            apply False.elim assump_29
            apply Or.inl
            intro assump_33
            have assump_69 : (p2 → True) := by
              intro assump_37
              apply True.intro
            let assump_36 := assump_21 assump_69
            apply False.elim assump_36
        case inr assump_15 =>
          cases assump_7
          case intro assump_45 assump_46 =>
            apply Or.inl
            apply And.intro
            intro assump_51
            have assump_70 : (p2 → True) := by
              intro assump_56
              apply True.intro
            let assump_55 := assump_46 assump_70
            apply False.elim assump_55
            apply Or.inl
            intro assump_60
            have assump_71 : (p2 → True) := by
              intro assump_64
              apply True.intro
            let assump_63 := assump_46 assump_71
            apply False.elim assump_63


variable (p0 p6 p4 p2 p7 p5 p3 : Prop)
theorem file94_70470 : ((((((p6 → False) ∨ (False → p6)) ∨ ((p0 ∨ True) ∧ (True ∨ p4))) ∨ (((p0 → False) → (p6 → False)) ∨ ((p3 → False) → (p6 → False)))) ∧ ((((False ∧ p6) → (p0 ∧ p4)) → False) ∧ (((p7 ∧ p4) ∨ (p5 ∧ p2)) ∨ ((p4 ∨ p2) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_12 assump_13 =>
            cases assump_13
            case inl assump_16 =>
              cases assump_16
              case inl assump_18 =>
                cases assump_18
                case intro assump_20 assump_21 =>
                  have assump_548 : ((False ∧ p6) → (p0 ∧ p4)) := by
                    intro assump_29
                    apply And.intro
                    cases assump_29
                    case intro assump_30 assump_31 =>
                      apply False.elim assump_30
                    cases assump_29
                    case intro assump_34 assump_35 =>
                      apply False.elim assump_34
                  let assump_28 := assump_12 assump_548
                  apply False.elim assump_28
              case inr assump_19 =>
                cases assump_19
                case intro assump_41 assump_42 =>
                  have assump_549 : ((False ∧ p6) → (p0 ∧ p4)) := by
                    intro assump_50
                    apply And.intro
                    cases assump_50
                    case intro assump_51 assump_52 =>
                      apply False.elim assump_51
                    cases assump_50
                    case intro assump_55 assump_56 =>
                      apply False.elim assump_55
                  let assump_49 := assump_12 assump_549
                  apply False.elim assump_49
            case inr assump_17 =>
              have assump_550 : ((False ∧ p6) → (p0 ∧ p4)) := by
                intro assump_66
                apply And.intro
                cases assump_66
                case intro assump_67 assump_68 =>
                  apply False.elim assump_67
                cases assump_66
                case intro assump_71 assump_72 =>
                  apply False.elim assump_71
              let assump_65 := assump_12 assump_550
              apply False.elim assump_65
        case inr assump_9 =>
          cases assump_3
          case intro assump_80 assump_81 =>
            cases assump_81
            case inl assump_84 =>
              cases assump_84
              case inl assump_86 =>
                cases assump_86
                case intro assump_88 assump_89 =>
                  have assump_551 : ((False ∧ p6) → (p0 ∧ p4)) := by
                    intro assump_97
                    apply And.intro
                    cases assump_97
                    case intro assump_98 assump_99 =>
                      apply False.elim assump_98
                    cases assump_97
                    case intro assump_102 assump_103 =>
                      apply False.elim assump_102
                  let assump_96 := assump_80 assump_551
                  apply False.elim assump_96
              case inr assump_87 =>
                cases assump_87
                case intro assump_109 assump_110 =>
                  have assump_552 : ((False ∧ p6) → (p0 ∧ p4)) := by
                    intro assump_118
                    apply And.intro
                    cases assump_118
                    case intro assump_119 assump_120 =>
                      apply False.elim assump_119
                    cases assump_118
                    case intro assump_123 assump_124 =>
                      apply False.elim assump_123
                  let assump_117 := assump_80 assump_552
                  apply False.elim assump_117
            case inr assump_85 =>
              have assump_553 : ((False ∧ p6) → (p0 ∧ p4)) := by
                intro assump_134
                apply And.intro
                cases assump_134
                case intro assump_135 assump_136 =>
                  apply False.elim assump_135
                cases assump_134
                case intro assump_139 assump_140 =>
                  apply False.elim assump_139
              let assump_133 := assump_80 assump_553
              apply False.elim assump_133
      case inr assump_7 =>
        cases assump_7
        case intro assump_146 assump_147 =>
          cases assump_146
          case inl assump_148 =>
            cases assump_147
            case inl assump_152 =>
              cases assump_3
              case intro assump_156 assump_157 =>
                cases assump_157
                case inl assump_160 =>
                  cases assump_160
                  case inl assump_162 =>
                    cases assump_162
                    case intro assump_164 assump_165 =>
                      have assump_554 : ((False ∧ p6) → (p0 ∧ p4)) := by
                        intro assump_173
                        apply And.intro
                        cases assump_173
                        case intro assump_174 assump_175 =>
                          apply False.elim assump_174
                        cases assump_173
                        case intro assump_178 assump_179 =>
                          apply False.elim assump_178
                      let assump_172 := assump_156 assump_554
                      apply False.elim assump_172
                  case inr assump_163 =>
                    cases assump_163
                    case intro assump_185 assump_186 =>
                      have assump_555 : ((False ∧ p6) → (p0 ∧ p4)) := by
                        intro assump_194
                        apply And.intro
                        cases assump_194
                        case intro assump_195 assump_196 =>
                          apply False.elim assump_195
                        cases assump_194
                        case intro assump_199 assump_200 =>
                          apply False.elim assump_199
                      let assump_193 := assump_156 assump_555
                      apply False.elim assump_193
                case inr assump_161 =>
                  have assump_556 : ((False ∧ p6) → (p0 ∧ p4)) := by
                    intro assump_210
                    apply And.intro
                    cases assump_210
                    case intro assump_211 assump_212 =>
                      apply False.elim assump_211
                    cases assump_210
                    case intro assump_215 assump_216 =>
                      apply False.elim assump_215
                  let assump_209 := assump_156 assump_556
                  apply False.elim assump_209
            case inr assump_153 =>
              cases assump_3
              case intro assump_224 assump_225 =>
                cases assump_225
                case inl assump_228 =>
                  cases assump_228
                  case inl assump_230 =>
                    cases assump_230
                    case intro assump_232 assump_233 =>
                      have assump_557 : ((False ∧ p6) → (p0 ∧ p4)) := by
                        intro assump_241
                        apply And.intro
                        cases assump_241
                        case intro assump_242 assump_243 =>
                          apply False.elim assump_242
                        cases assump_241
                        case intro assump_246 assump_247 =>
                          apply False.elim assump_246
                      let assump_240 := assump_224 assump_557
                      apply False.elim assump_240
                  case inr assump_231 =>
                    cases assump_231
                    case intro assump_253 assump_254 =>
                      have assump_558 : ((False ∧ p6) → (p0 ∧ p4)) := by
                        intro assump_262
                        apply And.intro
                        cases assump_262
                        case intro assump_263 assump_264 =>
                          apply False.elim assump_263
                        cases assump_262
                        case intro assump_267 assump_268 =>
                          apply False.elim assump_267
                      let assump_261 := assump_224 assump_558
                      apply False.elim assump_261
                case inr assump_229 =>
                  have assump_559 : (p4 ∨ p2) := by
                    apply Or.inl
                    exact assump_153
                  let assump_276 := assump_229 assump_559
                  apply False.elim assump_276
          case inr assump_149 =>
            cases assump_147
            case inl assump_282 =>
              cases assump_3
              case intro assump_286 assump_287 =>
                cases assump_287
                case inl assump_290 =>
                  cases assump_290
                  case inl assump_292 =>
                    cases assump_292
                    case intro assump_294 assump_295 =>
                      have assump_560 : ((False ∧ p6) → (p0 ∧ p4)) := by
                        intro assump_303
                        apply And.intro
                        cases assump_303
                        case intro assump_304 assump_305 =>
                          apply False.elim assump_304
                        cases assump_303
                        case intro assump_308 assump_309 =>
                          apply False.elim assump_308
                      let assump_302 := assump_286 assump_560
                      apply False.elim assump_302
                  case inr assump_293 =>
                    cases assump_293
                    case intro assump_315 assump_316 =>
                      have assump_561 : ((False ∧ p6) → (p0 ∧ p4)) := by
                        intro assump_324
                        apply And.intro
                        cases assump_324
                        case intro assump_325 assump_326 =>
                          apply False.elim assump_325
                        cases assump_324
                        case intro assump_329 assump_330 =>
                          apply False.elim assump_329
                      let assump_323 := assump_286 assump_561
                      apply False.elim assump_323
                case inr assump_291 =>
                  have assump_562 : ((False ∧ p6) → (p0 ∧ p4)) := by
                    intro assump_340
                    apply And.intro
                    cases assump_340
                    case intro assump_341 assump_342 =>
                      apply False.elim assump_341
                    cases assump_340
                    case intro assump_345 assump_346 =>
                      apply False.elim assump_345
                  let assump_339 := assump_286 assump_562
                  apply False.elim assump_339
            case inr assump_283 =>
              cases assump_3
              case intro assump_354 assump_355 =>
                cases assump_355
                case inl assump_358 =>
                  cases assump_358
                  case inl assump_360 =>
                    cases assump_360
                    case intro assump_362 assump_363 =>
                      have assump_563 : ((False ∧ p6) → (p0 ∧ p4)) := by
                        intro assump_371
                        apply And.intro
                        cases assump_371
                        case intro assump_372 assump_373 =>
                          apply False.elim assump_372
                        cases assump_371
                        case intro assump_376 assump_377 =>
                          apply False.elim assump_376
                      let assump_370 := assump_354 assump_563
                      apply False.elim assump_370
                  case inr assump_361 =>
                    cases assump_361
                    case intro assump_383 assump_384 =>
                      have assump_564 : ((False ∧ p6) → (p0 ∧ p4)) := by
                        intro assump_392
                        apply And.intro
                        cases assump_392
                        case intro assump_393 assump_394 =>
                          apply False.elim assump_393
                        cases assump_392
                        case intro assump_397 assump_398 =>
                          apply False.elim assump_397
                      let assump_391 := assump_354 assump_564
                      apply False.elim assump_391
                case inr assump_359 =>
                  have assump_565 : (p4 ∨ p2) := by
                    apply Or.inl
                    exact assump_283
                  let assump_406 := assump_359 assump_565
                  apply False.elim assump_406
    case inr assump_5 =>
      cases assump_5
      case inl assump_410 =>
        cases assump_3
        case intro assump_414 assump_415 =>
          cases assump_415
          case inl assump_418 =>
            cases assump_418
            case inl assump_420 =>
              cases assump_420
              case intro assump_422 assump_423 =>
                have assump_566 : ((False ∧ p6) → (p0 ∧ p4)) := by
                  intro assump_431
                  apply And.intro
                  cases assump_431
                  case intro assump_432 assump_433 =>
                    apply False.elim assump_432
                  cases assump_431
                  case intro assump_436 assump_437 =>
                    apply False.elim assump_436
                let assump_430 := assump_414 assump_566
                apply False.elim assump_430
            case inr assump_421 =>
              cases assump_421
              case intro assump_443 assump_444 =>
                have assump_567 : ((False ∧ p6) → (p0 ∧ p4)) := by
                  intro assump_452
                  apply And.intro
                  cases assump_452
                  case intro assump_453 assump_454 =>
                    apply False.elim assump_453
                  cases assump_452
                  case intro assump_457 assump_458 =>
                    apply False.elim assump_457
                let assump_451 := assump_414 assump_567
                apply False.elim assump_451
          case inr assump_419 =>
            have assump_568 : ((False ∧ p6) → (p0 ∧ p4)) := by
              intro assump_468
              apply And.intro
              cases assump_468
              case intro assump_469 assump_470 =>
                apply False.elim assump_469
              cases assump_468
              case intro assump_473 assump_474 =>
                apply False.elim assump_473
            let assump_467 := assump_414 assump_568
            apply False.elim assump_467
      case inr assump_411 =>
        cases assump_3
        case intro assump_482 assump_483 =>
          cases assump_483
          case inl assump_486 =>
            cases assump_486
            case inl assump_488 =>
              cases assump_488
              case intro assump_490 assump_491 =>
                have assump_569 : ((False ∧ p6) → (p0 ∧ p4)) := by
                  intro assump_499
                  apply And.intro
                  cases assump_499
                  case intro assump_500 assump_501 =>
                    apply False.elim assump_500
                  cases assump_499
                  case intro assump_504 assump_505 =>
                    apply False.elim assump_504
                let assump_498 := assump_482 assump_569
                apply False.elim assump_498
            case inr assump_489 =>
              cases assump_489
              case intro assump_511 assump_512 =>
                have assump_570 : ((False ∧ p6) → (p0 ∧ p4)) := by
                  intro assump_520
                  apply And.intro
                  cases assump_520
                  case intro assump_521 assump_522 =>
                    apply False.elim assump_521
                  cases assump_520
                  case intro assump_525 assump_526 =>
                    apply False.elim assump_525
                let assump_519 := assump_482 assump_570
                apply False.elim assump_519
          case inr assump_487 =>
            have assump_571 : ((False ∧ p6) → (p0 ∧ p4)) := by
              intro assump_536
              apply And.intro
              cases assump_536
              case intro assump_537 assump_538 =>
                apply False.elim assump_537
              cases assump_536
              case intro assump_541 assump_542 =>
                apply False.elim assump_541
            let assump_535 := assump_482 assump_571
            apply False.elim assump_535


variable (p3 p1 p7 : Prop)
theorem file94_87321 : (((((True ∨ p1) ∨ (False → False)) ∧ ((p3 ∨ p7) ∨ (p7 → p1))) → False) → False) := by
  intro assump_1
  have assump_16 : (((True ∨ p1) ∨ (False → False)) ∧ ((p3 ∨ p7) ∨ (p7 → p1))) := by
    apply And.intro
    apply Or.inl
    apply Or.inl
    apply True.intro
    apply Or.inr
    intro assump_5
    have assump_17 : (((True ∨ p1) ∨ (False → False)) ∧ ((p3 ∨ p7) ∨ (p7 → p1))) := by
      apply And.intro
      apply Or.inl
      apply Or.inl
      apply True.intro
      apply Or.inl
      apply Or.inr
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p3 p7 p1 p2 p5 p0 p6 : Prop)
theorem file94_88046 : (((((p0 → False) → False) → ((p5 → False) → (p0 ∨ p1))) → False) → ((((p7 ∧ p5) ∧ (p3 ∧ p2)) → False) → (((p1 ∧ p1) → (False → False)) ∨ ((p2 → p3) → (p6 → False))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  intro assump_8
  apply False.elim assump_8


variable (p4 p1 p3 p5 p7 p6 p2 : Prop)
theorem file94_88393 : (((((True → p3) → (False ∧ p7)) → ((p3 → p1) ∨ (True → False))) → (((False ∧ p5) ∧ (False ∧ p6)) → False)) ∨ ((((p3 ∧ p5) → False) ∨ ((False ∧ p3) → False)) ∨ (((p3 → p4) → (p7 → p1)) ∨ ((True ∨ p2) ∧ (p2 ∨ p4))))) := by
  apply Or.inl
  intro assump_12
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      apply False.elim assump_16


variable (p4 p1 p0 p2 p3 p5 p7 : Prop)
theorem file94_88873 : (((((p2 → False) → False) ∨ ((p7 → p5) → (False ∧ p0))) ∨ (((p5 ∨ p4) ∧ (p7 ∨ False)) → ((p7 ∨ p4) → False))) → ((((False ∧ p0) ∧ (p2 → p3)) ∧ ((p1 → False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p2 p1 p0 p4 p3 p5 : Prop)
theorem file94_89349 : (((((True → False) → (p4 ∨ p0)) ∨ ((p4 ∧ p2) ∧ (False → p3))) → False) → ((((p1 ∧ p5) → False) ∨ ((p3 ∨ True) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_35 : (((True → False) → (p4 ∨ p0)) ∨ ((p4 ∧ p2) ∧ (False → p3))) := by
      apply Or.inl
      intro assump_10
      have assump_36 : True := by
        apply True.intro
      let assump_13 := assump_10 assump_36
      apply False.elim assump_13
    let assump_9 := assump_1 assump_35
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_37 : (((True → False) → (p4 ∨ p0)) ∨ ((p4 ∧ p2) ∧ (False → p3))) := by
      apply Or.inl
      intro assump_25
      have assump_38 : True := by
        apply True.intro
      let assump_28 := assump_25 assump_38
      apply False.elim assump_28
    let assump_24 := assump_1 assump_37
    apply False.elim assump_24


variable (p0 p1 p7 p6 : Prop)
theorem file94_90302 : (((((p0 ∧ False) ∧ (p6 → True)) → ((p1 ∧ p7) → False)) → False) → False) := by
  intro assump_20
  have assump_43 : (((p0 ∧ False) ∧ (p6 → True)) → ((p1 ∧ p7) → False)) := by
    intro assump_24
    intro assump_25
    cases assump_25
    case intro assump_26 assump_27 =>
      cases assump_24
      case intro assump_32 assump_33 =>
        cases assump_32
        case intro assump_34 assump_35 =>
          apply False.elim assump_35
  let assump_23 := assump_20 assump_43
  apply False.elim assump_23


variable (p7 p2 p6 p5 p3 : Prop)
theorem file94_90865 : ((((((True → False) → (p5 → False)) → False) → (((p7 ∨ p6) ∨ (p3 ∧ p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_72 : ((((True → False) → (p5 → False)) → False) → (((p7 ∨ p6) ∨ (p3 ∧ p2)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        have assump_73 : ((True → False) → (p5 → False)) := by
          intro assump_16
          intro assump_17
          have assump_74 : True := by
            apply True.intro
          let assump_22 := assump_16 assump_74
          apply False.elim assump_22
        let assump_15 := assump_5 assump_73
        apply False.elim assump_15
      case inr assump_10 =>
        have assump_75 : ((True → False) → (p5 → False)) := by
          intro assump_34
          intro assump_35
          have assump_76 : True := by
            apply True.intro
          let assump_40 := assump_34 assump_76
          apply False.elim assump_40
        let assump_33 := assump_5 assump_75
        apply False.elim assump_33
    case inr assump_8 =>
      cases assump_8
      case intro assump_47 assump_48 =>
        have assump_77 : ((True → False) → (p5 → False)) := by
          intro assump_56
          intro assump_57
          have assump_78 : True := by
            apply True.intro
          let assump_62 := assump_56 assump_78
          apply False.elim assump_62
        let assump_55 := assump_5 assump_77
        apply False.elim assump_55
  let assump_4 := assump_1 assump_72
  apply False.elim assump_4


variable (p1 p7 p5 p6 p4 p3 p2 : Prop)
theorem file94_92500 : (((((p4 ∨ p3) → False) → False) → False) → ((((True → False) ∧ (p4 → p1)) → ((p5 ∨ p4) ∨ (p6 → False))) ∨ (((p4 ∨ p7) → False) → ((p2 → False) ∨ (p2 ∨ False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inr
    intro assump_11
    have assump_20 : True := by
      apply True.intro
    let assump_16 := assump_5 assump_20
    apply False.elim assump_16


variable (p4 p1 p5 p2 p7 p6 p3 : Prop)
theorem file94_92994 : (((((p5 ∧ p5) → (False → p2)) ∨ ((p4 → False) → (p2 ∧ p1))) → False) → ((((p3 ∧ p6) ∨ (True → False)) → False) → (((p3 ∨ p7) ∧ (p1 ∨ p6)) → ((p5 → False) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      cases assump_8
      case inl assump_13 =>
        have assump_75 : (((p5 ∧ p5) → (False → p2)) ∨ ((p4 → False) → (p2 ∧ p1))) := by
          apply Or.inl
          intro assump_22
          intro assump_23
          apply False.elim assump_23
        let assump_21 := assump_1 assump_75
        apply False.elim assump_21
      case inr assump_14 =>
        have assump_76 : (((p5 ∧ p5) → (False → p2)) ∨ ((p4 → False) → (p2 ∧ p1))) := by
          apply Or.inl
          intro assump_36
          intro assump_37
          apply False.elim assump_37
        let assump_35 := assump_1 assump_76
        apply False.elim assump_35
    case inr assump_10 =>
      cases assump_8
      case inl assump_45 =>
        have assump_77 : (((p5 ∧ p5) → (False → p2)) ∨ ((p4 → False) → (p2 ∧ p1))) := by
          apply Or.inl
          intro assump_54
          intro assump_55
          apply False.elim assump_55
        let assump_53 := assump_1 assump_77
        apply False.elim assump_53
      case inr assump_46 =>
        have assump_78 : (((p5 ∧ p5) → (False → p2)) ∨ ((p4 → False) → (p2 ∧ p1))) := by
          apply Or.inl
          intro assump_68
          intro assump_69
          apply False.elim assump_69
        let assump_67 := assump_1 assump_78
        apply False.elim assump_67


variable (p1 p0 p2 p6 p5 p4 : Prop)
theorem file94_94689 : (((((p4 ∨ p0) → (p1 ∨ True)) → False) ∨ (((p4 → False) → (True ∨ p0)) ∧ ((True ∧ p6) → False))) → ((((True → False) → (p4 ∨ p5)) ∨ ((p5 ∨ p6) → False)) ∨ (((p0 ∨ p0) → False) → ((p4 ∧ p2) ∧ (p1 ∨ p6))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    have assump_26 : True := by
      apply True.intro
    let assump_9 := assump_6 assump_26
    apply False.elim assump_9
  case inr assump_3 =>
    cases assump_3
    case intro assump_13 assump_14 =>
      apply Or.inl
      apply Or.inl
      intro assump_19
      have assump_27 : True := by
        apply True.intro
      let assump_22 := assump_19 assump_27
      apply False.elim assump_22


variable (p2 p5 p4 p7 : Prop)
theorem file94_95462 : (((((p5 → False) ∧ (p2 ∧ p5)) ∧ ((True → True) ∧ (p7 ∧ p4))) ∧ (((False → False) ∨ (False ∧ p7)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_5
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              have assump_35 : ((False → False) ∨ (False ∧ p7)) := by
                apply Or.inl
                intro assump_29
                apply False.elim assump_29
              let assump_28 := assump_3 assump_35
              apply False.elim assump_28


variable (p6 p2 p4 p5 p1 p7 p3 p0 : Prop)
theorem file94_96305 : (((((p4 → False) ∨ (True ∧ p2)) → ((False ∧ p6) → False)) ∨ (((p7 → False) → False) → False)) ∨ ((((p2 ∧ p4) ∧ (p2 → p0)) → ((p5 → p1) ∧ (False ∨ p2))) ∨ (((p6 ∧ p6) → (True → p6)) → ((p3 ∨ p3) ∧ (p1 → p3))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3


variable (p7 p2 p3 p1 p0 p4 p6 : Prop)
theorem file94_96729 : (((((p6 ∧ p6) → (p1 → p3)) ∧ ((p4 ∧ p3) → False)) → (((p7 → False) ∧ (p2 → False)) → False)) → ((((p4 ∨ True) → False) → ((False ∧ p3) ∧ (p4 ∧ p7))) ∨ (((p2 ∨ p0) → (p2 ∨ p6)) → False))) := by
  intro assump_16
  apply Or.inl
  intro assump_19
  apply And.intro
  apply And.intro
  have assump_44 : (p4 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_22 := assump_19 assump_44
  apply False.elim assump_22
  have assump_45 : (p4 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_28 := assump_19 assump_45
  apply False.elim assump_28
  apply And.intro
  have assump_46 : (p4 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_34 := assump_19 assump_46
  apply False.elim assump_34
  have assump_47 : (p4 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_40 := assump_19 assump_47
  apply False.elim assump_40


variable (p6 p2 p0 p4 p5 : Prop)
theorem file94_97656 : (((((p6 → False) ∧ (p2 ∧ p0)) ∧ ((p4 ∨ p0) → False)) ∧ (((p5 ∧ p5) ∧ (p4 → False)) ∨ ((p0 → p5) ∧ (p5 → p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_3
          case inl assump_18 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                have assump_50 : (p4 ∨ p0) := by
                  apply Or.inr
                  exact assump_11
                let assump_33 := assump_5 assump_50
                apply False.elim assump_33
          case inr assump_19 =>
            cases assump_19
            case intro assump_37 assump_38 =>
              have assump_51 : (p4 ∨ p0) := by
                apply Or.inr
                exact assump_11
              let assump_46 := assump_5 assump_51
              apply False.elim assump_46


variable (p4 p1 p3 p2 p7 p5 : Prop)
theorem file94_98812 : (((((p5 → p7) → False) ∨ ((p5 → False) ∨ (p1 ∧ p2))) → (((False ∧ p5) ∧ (p2 ∧ p5)) → False)) ∨ ((((p1 ∨ p4) → False) ∨ ((p5 ∨ p5) ∧ (p5 ∧ p3))) ∧ (((p3 ∨ p3) → (False ∨ p3)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5


variable (p5 p4 p2 p1 p7 p3 : Prop)
theorem file94_99250 : (((((False → False) ∨ (p5 → False)) → ((True → False) ∧ (p7 → False))) → (((p4 → p1) ∨ (p2 ∧ p2)) ∨ ((True ∧ p3) → False))) ∨ ((((p7 → p3) → False) → False) ∨ (((p5 → p1) ∨ (p1 → False)) → ((p2 ∧ False) ∧ (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  have assump_17 : ((False → False) ∨ (p5 → False)) := by
    apply Or.inl
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_1 assump_17
  let assump_12 := And.left assump_8
  have assump_18 : True := by
    apply True.intro
  let assump_13 := assump_12 assump_18
  apply False.elim assump_13


variable (p5 p4 p6 p1 p7 p0 : Prop)
theorem file94_99934 : ((((((p5 ∧ p4) ∨ (p6 → p4)) ∧ ((p5 ∨ p4) → (p5 → False))) → (((p7 ∨ p0) → (p0 ∧ True)) → ((p1 ∧ True) → (p7 → p7)))) → False) → False) := by
  intro assump_1
  have assump_38 : ((((p5 ∧ p4) ∨ (p6 → p4)) ∧ ((p5 ∨ p4) → (p5 → False))) → (((p7 ∨ p0) → (p0 ∧ True)) → ((p1 ∧ True) → (p7 → p7)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      cases assump_5
      case intro assump_19 assump_20 =>
        cases assump_19
        case inl assump_21 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            exact assump_8
        case inr assump_22 =>
          exact assump_8
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p6 p0 p1 p5 p3 p2 : Prop)
theorem file94_100757 : ((((((p5 ∨ p0) ∨ (p1 ∨ p6)) ∧ ((p3 ∧ False) ∧ (p6 ∧ p2))) → (((p6 → False) → False) → False)) → False) → False) := by
  intro assump_20
  have assump_79 : ((((p5 ∨ p0) ∨ (p1 ∨ p6)) ∧ ((p3 ∧ False) ∧ (p6 ∧ p2))) → (((p6 → False) → False) → False)) := by
    intro assump_24
    intro assump_25
    cases assump_24
    case intro assump_28 assump_29 =>
      cases assump_28
      case inl assump_30 =>
        cases assump_30
        case inl assump_32 =>
          cases assump_29
          case intro assump_36 assump_37 =>
            cases assump_36
            case intro assump_38 assump_39 =>
              apply False.elim assump_39
        case inr assump_33 =>
          cases assump_29
          case intro assump_46 assump_47 =>
            cases assump_46
            case intro assump_48 assump_49 =>
              apply False.elim assump_49
      case inr assump_31 =>
        cases assump_31
        case inl assump_54 =>
          cases assump_29
          case intro assump_58 assump_59 =>
            cases assump_58
            case intro assump_60 assump_61 =>
              apply False.elim assump_61
        case inr assump_55 =>
          cases assump_29
          case intro assump_68 assump_69 =>
            cases assump_68
            case intro assump_70 assump_71 =>
              apply False.elim assump_71
  let assump_23 := assump_20 assump_79
  apply False.elim assump_23


variable (p6 p2 p0 p5 p4 p3 p7 : Prop)
theorem file94_102225 : (((((p4 → False) → False) ∨ ((p2 → False) → (p7 ∧ False))) ∨ (((p0 ∨ p3) → False) → False)) → ((((p6 ∨ False) ∧ (True → p7)) → False) → (((p3 → False) → (p0 → False)) → ((False → False) ∨ (p5 → p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    cases assump_8
    case inl assump_10 =>
      apply Or.inl
      intro assump_14
      apply False.elim assump_14
    case inr assump_11 =>
      apply Or.inl
      intro assump_19
      apply False.elim assump_19
  case inr assump_9 =>
    apply Or.inl
    intro assump_24
    apply False.elim assump_24


variable (p3 p1 p0 p4 : Prop)
theorem file94_102888 : ((((((p0 → p1) ∧ (p4 → p1)) → ((True → False) → False)) ∧ (((p0 ∨ p4) ∨ (p4 → False)) ∨ ((p3 ∨ p4) → (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_49 : ((((p0 → p1) ∧ (p4 → p1)) → ((True → False) → False)) ∧ (((p0 ∨ p4) ∨ (p4 → False)) ∨ ((p3 ∨ p4) → (p0 → False)))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      have assump_50 : True := by
        apply True.intro
      let assump_17 := assump_6 assump_50
      apply False.elim assump_17
    apply Or.inl
    apply Or.inr
    intro assump_21
    have assump_51 : ((((p0 → p1) ∧ (p4 → p1)) → ((True → False) → False)) ∧ (((p0 ∨ p4) ∨ (p4 → False)) ∨ ((p3 ∨ p4) → (p0 → False)))) := by
      apply And.intro
      intro assump_26
      intro assump_27
      cases assump_26
      case intro assump_30 assump_31 =>
        have assump_52 : True := by
          apply True.intro
        let assump_39 := assump_27 assump_52
        apply False.elim assump_39
      apply Or.inl
      apply Or.inl
      apply Or.inr
      exact assump_21
    let assump_25 := assump_1 assump_51
    apply False.elim assump_25
  let assump_4 := assump_1 assump_49
  apply False.elim assump_4


variable (p7 p6 p4 p5 p3 p2 p1 : Prop)
theorem file94_104179 : (((((p2 → p3) → (p4 ∧ False)) ∧ ((True → False) → False)) → (((False ∧ False) ∨ (p2 → True)) ∨ ((True ∧ False) ∧ (p6 ∨ p1)))) ∨ ((((p2 → False) ∨ (p5 → False)) ∨ ((p2 ∨ p2) → False)) → (((p2 → p7) ∧ (p7 ∨ False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inr
    intro assump_8
    apply True.intro


variable (p0 p6 p2 p7 p1 : Prop)
theorem file94_104623 : (((((False → False) ∨ (p1 → p0)) ∨ ((p7 ∧ p7) → (p2 ∧ p6))) → False) → False) := by
  intro assump_1
  have assump_11 : (((False → False) ∨ (p1 → p0)) ∨ ((p7 ∧ p7) → (p2 ∧ p6))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p7 p6 p5 p1 : Prop)
theorem file94_105012 : (((((True ∨ True) → False) ∨ ((False → p1) → False)) → False) ∨ ((((p7 ∨ False) → (p4 ∧ p1)) ∨ ((p5 → p1) → False)) ∧ (((p5 ∧ False) ∧ (False → p6)) → ((p6 ∧ p6) → (p7 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_19 : (True ∨ True) := by
      apply Or.inl
      apply True.intro
    let assump_6 := assump_2 assump_19
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_20 : (False → p1) := by
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_3 assump_20
    apply False.elim assump_12


variable (p3 p4 p6 p5 p0 p1 p2 p7 : Prop)
theorem file94_105678 : (((((p6 → p3) → (False → False)) → False) → (((p1 ∨ p6) ∧ (p7 → False)) → False)) ∨ ((((p3 ∧ p1) → (p2 → False)) → False) → (((True ∧ p4) → (p0 ∧ p0)) ∨ ((p5 ∧ p1) ∨ (p4 ∧ p7))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      have assump_35 : ((p6 → p3) → (False → False)) := by
        intro assump_14
        intro assump_15
        apply False.elim assump_15
      let assump_13 := assump_1 assump_35
      apply False.elim assump_13
    case inr assump_6 =>
      have assump_36 : ((p6 → p3) → (False → False)) := by
        intro assump_28
        intro assump_29
        apply False.elim assump_29
      let assump_27 := assump_1 assump_36
      apply False.elim assump_27


variable (p7 p4 p5 p6 p1 p0 p2 p3 : Prop)
theorem file94_106533 : (((((p5 ∨ p4) ∨ (False → False)) ∨ ((True → p5) ∨ (p1 → p4))) ∨ (((p0 → p0) ∨ (p5 ∧ p3)) → False)) → ((((True ∨ p3) → (p6 → p2)) → False) → (((True → False) → False) ∨ ((p1 ∨ p7) → (False → True))))) := by
  intro assump_5
  intro assump_6
  cases assump_5
  case inl assump_9 =>
    cases assump_9
    case inl assump_11 =>
      cases assump_11
      case inl assump_13 =>
        cases assump_13
        case inl assump_15 =>
          apply Or.inl
          intro assump_19
          have assump_73 : True := by
            apply True.intro
          let assump_22 := assump_19 assump_73
          apply False.elim assump_22
        case inr assump_16 =>
          apply Or.inl
          intro assump_28
          have assump_74 : True := by
            apply True.intro
          let assump_31 := assump_28 assump_74
          apply False.elim assump_31
      case inr assump_14 =>
        apply Or.inl
        intro assump_37
        have assump_75 : True := by
          apply True.intro
        let assump_40 := assump_37 assump_75
        apply False.elim assump_40
    case inr assump_12 =>
      cases assump_12
      case inl assump_44 =>
        apply Or.inl
        intro assump_48
        have assump_76 : True := by
          apply True.intro
        let assump_51 := assump_48 assump_76
        apply False.elim assump_51
      case inr assump_45 =>
        apply Or.inl
        intro assump_57
        have assump_77 : True := by
          apply True.intro
        let assump_60 := assump_57 assump_77
        apply False.elim assump_60
  case inr assump_10 =>
    apply Or.inl
    intro assump_66
    have assump_78 : True := by
      apply True.intro
    let assump_69 := assump_66 assump_78
    apply False.elim assump_69


variable (p4 p1 p6 p0 : Prop)
theorem file94_108330 : (((((p4 ∧ p0) → (p6 ∨ p0)) → False) → False) ∨ ((((p1 → p1) → False) ∨ ((p6 → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((p4 ∧ p0) → (p6 ∨ p0)) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      exact assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p3 p1 p0 p4 : Prop)
theorem file94_108758 : ((((((True → False) ∧ (p1 ∧ p0)) ∨ ((p1 → False) ∧ (p3 ∨ p6))) → (((p1 ∨ p3) ∧ (p4 ∧ p1)) → False)) → False) → False) := by
  intro assump_10
  have assump_115 : ((((True → False) ∧ (p1 ∧ p0)) ∨ ((p1 → False) ∧ (p3 ∨ p6))) → (((p1 ∨ p3) ∧ (p4 ∧ p1)) → False)) := by
    intro assump_14
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      cases assump_16
      case inl assump_18 =>
        cases assump_17
        case intro assump_22 assump_23 =>
          cases assump_14
          case inl assump_28 =>
            cases assump_28
            case intro assump_30 assump_31 =>
              cases assump_31
              case intro assump_34 assump_35 =>
                have assump_116 : True := by
                  apply True.intro
                let assump_42 := assump_30 assump_116
                apply False.elim assump_42
          case inr assump_29 =>
            cases assump_29
            case intro assump_46 assump_47 =>
              cases assump_47
              case inl assump_50 =>
                have assump_117 : p1 := by
                  exact assump_23
                let assump_55 := assump_46 assump_117
                apply False.elim assump_55
              case inr assump_51 =>
                have assump_118 : p1 := by
                  exact assump_23
                let assump_62 := assump_46 assump_118
                apply False.elim assump_62
      case inr assump_19 =>
        cases assump_17
        case intro assump_68 assump_69 =>
          cases assump_14
          case inl assump_74 =>
            cases assump_74
            case intro assump_76 assump_77 =>
              cases assump_77
              case intro assump_80 assump_81 =>
                have assump_119 : True := by
                  apply True.intro
                let assump_88 := assump_76 assump_119
                apply False.elim assump_88
          case inr assump_75 =>
            cases assump_75
            case intro assump_92 assump_93 =>
              cases assump_93
              case inl assump_96 =>
                have assump_120 : p1 := by
                  exact assump_69
                let assump_101 := assump_92 assump_120
                apply False.elim assump_101
              case inr assump_97 =>
                have assump_121 : p1 := by
                  exact assump_69
                let assump_108 := assump_92 assump_121
                apply False.elim assump_108
  let assump_13 := assump_10 assump_115
  apply False.elim assump_13


variable (p6 p0 p1 p5 p4 p7 p2 : Prop)
theorem file94_111354 : (((((True → False) → (p0 ∨ True)) → False) → (((p6 → p0) ∨ (p1 ∧ p4)) → ((p1 ∧ p7) ∧ (True → False)))) → ((((p2 → False) → False) → False) → (((p5 → False) ∨ (False → False)) → ((p7 ∧ p1) ∨ (False → False))))) := by
  intro assump_11
  intro assump_12
  intro assump_13
  cases assump_13
  case inl assump_14 =>
    apply Or.inr
    intro assump_22
    apply False.elim assump_22
  case inr assump_15 =>
    apply Or.inr
    intro assump_31
    apply False.elim assump_31


variable (p4 p1 p2 p0 p5 p6 p3 : Prop)
theorem file94_111889 : ((((((p1 → False) → (p1 ∨ p4)) ∧ ((p5 ∧ p0) ∨ (p6 → p1))) ∧ (((True ∨ p4) ∧ (p4 → False)) ∧ ((p5 → False) → False))) ∧ ((((p1 ∧ p6) ∨ (False → p3)) → False) ∧ (((True → False) ∨ (True ∨ p1)) ∧ ((p0 → False) ∧ (p2 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_5
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_20
                case inl assump_22 =>
                  cases assump_3
                  case intro assump_30 assump_31 =>
                    cases assump_31
                    case intro assump_34 assump_35 =>
                      cases assump_34
                      case inl assump_36 =>
                        cases assump_35
                        case intro assump_40 assump_41 =>
                          have assump_272 : p0 := by
                            exact assump_13
                          let assump_47 := assump_40 assump_272
                          apply False.elim assump_47
                      case inr assump_37 =>
                        cases assump_37
                        case inl assump_51 =>
                          cases assump_35
                          case intro assump_55 assump_56 =>
                            have assump_273 : p0 := by
                              exact assump_13
                            let assump_62 := assump_55 assump_273
                            apply False.elim assump_62
                        case inr assump_52 =>
                          cases assump_35
                          case intro assump_68 assump_69 =>
                            have assump_274 : p0 := by
                              exact assump_13
                            let assump_75 := assump_68 assump_274
                            apply False.elim assump_75
                case inr assump_23 =>
                  cases assump_3
                  case intro assump_85 assump_86 =>
                    cases assump_86
                    case intro assump_89 assump_90 =>
                      cases assump_89
                      case inl assump_91 =>
                        cases assump_90
                        case intro assump_95 assump_96 =>
                          have assump_275 : p0 := by
                            exact assump_13
                          let assump_102 := assump_95 assump_275
                          apply False.elim assump_102
                      case inr assump_92 =>
                        cases assump_92
                        case inl assump_106 =>
                          cases assump_90
                          case intro assump_110 assump_111 =>
                            have assump_276 : p0 := by
                              exact assump_13
                            let assump_117 := assump_110 assump_276
                            apply False.elim assump_117
                        case inr assump_107 =>
                          cases assump_90
                          case intro assump_123 assump_124 =>
                            have assump_277 : p0 := by
                              exact assump_13
                            let assump_130 := assump_123 assump_277
                            apply False.elim assump_130
        case inr assump_11 =>
          cases assump_5
          case intro assump_136 assump_137 =>
            cases assump_136
            case intro assump_138 assump_139 =>
              cases assump_138
              case inl assump_140 =>
                cases assump_3
                case intro assump_148 assump_149 =>
                  cases assump_149
                  case intro assump_152 assump_153 =>
                    cases assump_152
                    case inl assump_154 =>
                      cases assump_153
                      case intro assump_158 assump_159 =>
                        have assump_278 : True := by
                          apply True.intro
                        let assump_166 := assump_154 assump_278
                        apply False.elim assump_166
                    case inr assump_155 =>
                      cases assump_155
                      case inl assump_170 =>
                        cases assump_153
                        case intro assump_174 assump_175 =>
                          have assump_279 : ((p1 ∧ p6) ∨ (False → p3)) := by
                            apply Or.inr
                            intro assump_183
                            apply False.elim assump_183
                          let assump_182 := assump_148 assump_279
                          apply False.elim assump_182
                      case inr assump_171 =>
                        cases assump_153
                        case intro assump_191 assump_192 =>
                          have assump_280 : ((p1 ∧ p6) ∨ (False → p3)) := by
                            apply Or.inr
                            intro assump_201
                            apply False.elim assump_201
                          let assump_200 := assump_148 assump_280
                          apply False.elim assump_200
              case inr assump_141 =>
                cases assump_3
                case intro assump_213 assump_214 =>
                  cases assump_214
                  case intro assump_217 assump_218 =>
                    cases assump_217
                    case inl assump_219 =>
                      cases assump_218
                      case intro assump_223 assump_224 =>
                        have assump_281 : True := by
                          apply True.intro
                        let assump_231 := assump_219 assump_281
                        apply False.elim assump_231
                    case inr assump_220 =>
                      cases assump_220
                      case inl assump_235 =>
                        cases assump_218
                        case intro assump_239 assump_240 =>
                          have assump_282 : ((p1 ∧ p6) ∨ (False → p3)) := by
                            apply Or.inr
                            intro assump_248
                            apply False.elim assump_248
                          let assump_247 := assump_213 assump_282
                          apply False.elim assump_247
                      case inr assump_236 =>
                        cases assump_218
                        case intro assump_256 assump_257 =>
                          have assump_283 : ((p1 ∧ p6) ∨ (False → p3)) := by
                            apply Or.inr
                            intro assump_266
                            apply False.elim assump_266
                          let assump_265 := assump_213 assump_283
                          apply False.elim assump_265


variable (p5 p2 p3 p4 p6 p7 p0 : Prop)
theorem file94_119066 : ((((((False ∧ p2) ∧ (p6 ∨ True)) ∧ ((p2 → p0) ∨ (p3 ∧ p3))) ∧ (((p3 → False) ∨ (p7 ∧ True)) → False)) ∧ ((((p0 → p4) → False) ∧ ((p5 ∧ False) ∧ (p6 ∧ True))) → False)) → False) := by
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


variable (p2 p7 p5 p1 p6 p3 p0 p4 : Prop)
theorem file94_119668 : ((((((p5 → p7) → False) ∨ ((p1 ∨ p2) ∧ (p4 → False))) ∧ (((p1 ∨ False) → (p2 ∧ p6)) ∧ ((True → p3) ∧ (p6 ∧ False)))) ∨ ((((p2 ∨ p3) → (p7 → p0)) ∧ ((p5 ∨ p5) → (p2 ∨ p3))) ∧ (((False → False) ∨ (p3 ∨ p2)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              apply False.elim assump_19
      case inr assump_7 =>
        cases assump_7
        case intro assump_24 assump_25 =>
          cases assump_24
          case inl assump_26 =>
            cases assump_5
            case intro assump_32 assump_33 =>
              cases assump_33
              case intro assump_36 assump_37 =>
                cases assump_37
                case intro assump_40 assump_41 =>
                  apply False.elim assump_41
          case inr assump_27 =>
            cases assump_5
            case intro assump_50 assump_51 =>
              cases assump_51
              case intro assump_54 assump_55 =>
                cases assump_55
                case intro assump_58 assump_59 =>
                  apply False.elim assump_59
  case inr assump_3 =>
    cases assump_3
    case intro assump_64 assump_65 =>
      cases assump_64
      case intro assump_66 assump_67 =>
        have assump_81 : ((False → False) ∨ (p3 ∨ p2)) := by
          apply Or.inl
          intro assump_75
          apply False.elim assump_75
        let assump_74 := assump_65 assump_81
        apply False.elim assump_74


variable (p1 p6 p0 p3 p2 : Prop)
theorem file94_121473 : ((((((p1 ∨ p1) → False) → ((False ∧ True) → False)) → False) ∨ ((((p3 ∧ p3) → False) ∨ ((p2 → False) → (p6 ∧ False))) ∧ (((False ∧ p0) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_46 : (((p1 ∨ p1) → False) → ((False ∧ True) → False)) := by
      intro assump_7
      intro assump_8
      cases assump_8
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
    let assump_6 := assump_2 assump_46
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_16 assump_17 =>
      cases assump_16
      case inl assump_18 =>
        have assump_47 : ((False ∧ p0) → False) := by
          intro assump_25
          cases assump_25
          case intro assump_26 assump_27 =>
            apply False.elim assump_26
        let assump_24 := assump_17 assump_47
        apply False.elim assump_24
      case inr assump_19 =>
        have assump_48 : ((False ∧ p0) → False) := by
          intro assump_38
          cases assump_38
          case intro assump_39 assump_40 =>
            apply False.elim assump_39
        let assump_37 := assump_17 assump_48
        apply False.elim assump_37


variable (p0 p5 p7 p2 p1 p4 : Prop)
theorem file94_122737 : ((((((p1 ∧ p7) ∧ (p7 ∨ p5)) → ((p1 ∨ p0) ∨ (p4 ∧ p0))) ∨ (((p1 → p2) → False) ∧ ((p1 ∨ p5) ∧ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p1 ∧ p7) ∧ (p7 ∨ p5)) → ((p1 ∨ p0) ∨ (p4 ∧ p0))) ∨ (((p1 → p2) → False) ∧ ((p1 ∨ p5) ∧ (False → False)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply Or.inl
          apply Or.inl
          exact assump_8
        case inr assump_15 =>
          apply Or.inl
          apply Or.inl
          exact assump_8
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p2 p7 p0 p3 p1 p5 : Prop)
theorem file94_123525 : ((((((p3 → p1) ∨ (p2 ∧ p1)) ∨ ((p2 ∨ True) ∨ (p0 ∨ p7))) → (((False → p7) ∨ (p2 ∨ True)) ∨ ((p5 ∨ p5) → False))) → False) → False) := by
  intro assump_1
  have assump_53 : ((((p3 → p1) ∨ (p2 ∧ p1)) ∨ ((p2 ∨ True) ∨ (p0 ∨ p7))) → (((False → p7) ∨ (p2 ∨ True)) ∨ ((p5 ∨ p5) → False))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        apply Or.inl
        intro assump_12
        apply False.elim assump_12
      case inr assump_9 =>
        cases assump_9
        case intro assump_15 assump_16 =>
          apply Or.inl
          apply Or.inl
          intro assump_21
          apply False.elim assump_21
    case inr assump_7 =>
      cases assump_7
      case inl assump_24 =>
        cases assump_24
        case inl assump_26 =>
          apply Or.inl
          apply Or.inl
          intro assump_30
          apply False.elim assump_30
        case inr assump_27 =>
          apply Or.inl
          apply Or.inl
          intro assump_35
          apply False.elim assump_35
      case inr assump_25 =>
        cases assump_25
        case inl assump_38 =>
          apply Or.inl
          apply Or.inl
          intro assump_42
          apply False.elim assump_42
        case inr assump_39 =>
          apply Or.inl
          apply Or.inl
          intro assump_47
          apply False.elim assump_47
  let assump_4 := assump_1 assump_53
  apply False.elim assump_4


variable (p2 p1 p4 p7 p0 p5 p6 : Prop)
theorem file94_125062 : (((((True → False) ∨ (p4 → False)) → ((p6 ∨ p2) → False)) ∧ (((p6 ∨ p2) ∧ (p7 ∨ p1)) ∧ ((p1 ∨ False) → (p1 → False)))) → ((((p2 ∨ True) → False) → ((p5 → False) → (False → False))) ∨ (((p5 ∧ p5) → (p0 → p1)) ∧ ((p2 ∨ p0) → False)))) := by
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
          case inl assump_14 =>
            apply Or.inl
            intro assump_20
            intro assump_21
            intro assump_22
            apply False.elim assump_22
          case inr assump_15 =>
            apply Or.inl
            intro assump_29
            intro assump_30
            intro assump_31
            apply False.elim assump_31
        case inr assump_11 =>
          cases assump_9
          case inl assump_36 =>
            apply Or.inl
            intro assump_42
            intro assump_43
            intro assump_44
            apply False.elim assump_44
          case inr assump_37 =>
            apply Or.inl
            intro assump_51
            intro assump_52
            intro assump_53
            apply False.elim assump_53


variable (p6 p7 p3 p1 p0 p2 p5 p4 : Prop)
theorem file94_126402 : (((((p4 → p7) ∧ (p5 ∨ p4)) ∧ ((p4 ∧ False) ∧ (True ∧ p2))) ∧ (((p6 ∧ p2) ∧ (p2 ∨ p3)) ∨ ((p1 → p1) ∨ (p2 ∨ p2)))) → ((((True → True) ∧ (p7 → p7)) → ((p5 ∧ p2) ∨ (p0 → False))) ∧ (((p4 ∧ p4) → False) → ((p3 → False) ∧ (p2 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_14
          case inl assump_17 =>
            cases assump_12
            case intro assump_21 assump_22 =>
              cases assump_21
              case intro assump_23 assump_24 =>
                apply False.elim assump_24
          case inr assump_18 =>
            cases assump_12
            case intro assump_31 assump_32 =>
              cases assump_31
              case intro assump_33 assump_34 =>
                apply False.elim assump_34
  intro assump_39
  apply And.intro
  intro assump_40
  cases assump_1
  case intro assump_45 assump_46 =>
    cases assump_45
    case intro assump_47 assump_48 =>
      cases assump_47
      case intro assump_49 assump_50 =>
        cases assump_50
        case inl assump_53 =>
          cases assump_48
          case intro assump_57 assump_58 =>
            cases assump_57
            case intro assump_59 assump_60 =>
              apply False.elim assump_60
        case inr assump_54 =>
          cases assump_48
          case intro assump_67 assump_68 =>
            cases assump_67
            case intro assump_69 assump_70 =>
              apply False.elim assump_70
  intro assump_75
  cases assump_1
  case intro assump_80 assump_81 =>
    cases assump_80
    case intro assump_82 assump_83 =>
      cases assump_82
      case intro assump_84 assump_85 =>
        cases assump_85
        case inl assump_88 =>
          cases assump_83
          case intro assump_92 assump_93 =>
            cases assump_92
            case intro assump_94 assump_95 =>
              apply False.elim assump_95
        case inr assump_89 =>
          cases assump_83
          case intro assump_102 assump_103 =>
            cases assump_102
            case intro assump_104 assump_105 =>
              apply False.elim assump_105


