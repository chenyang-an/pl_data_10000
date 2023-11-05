variable (p2 p3 p0 p6 p7 p4 p1 : Prop)
theorem file21_47 : (((((p1 ∧ p7) → (True ∨ p4)) → ((False → False) → (p3 → True))) ∧ (((p3 ∨ p4) ∨ (p6 ∨ True)) ∧ ((False ∧ p0) ∧ (False → p2)))) → False) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_12
    case intro assump_15 assump_16 =>
      cases assump_15
      case inl assump_17 =>
        cases assump_17
        case inl assump_19 =>
          cases assump_16
          case intro assump_23 assump_24 =>
            cases assump_23
            case intro assump_25 assump_26 =>
              apply False.elim assump_25
        case inr assump_20 =>
          cases assump_16
          case intro assump_31 assump_32 =>
            cases assump_31
            case intro assump_33 assump_34 =>
              apply False.elim assump_33
      case inr assump_18 =>
        cases assump_18
        case inl assump_37 =>
          cases assump_16
          case intro assump_41 assump_42 =>
            cases assump_41
            case intro assump_43 assump_44 =>
              apply False.elim assump_43
        case inr assump_38 =>
          cases assump_16
          case intro assump_49 assump_50 =>
            cases assump_49
            case intro assump_51 assump_52 =>
              apply False.elim assump_51


variable (p0 p3 p1 p5 p7 p6 p4 : Prop)
theorem file21_1368 : ((((((p3 → False) ∧ (p0 ∨ p3)) → ((p0 → False) ∧ (p5 ∧ p4))) → (((True ∧ p7) ∨ (p6 ∨ p1)) ∨ ((True → False) → (p3 ∧ p3)))) → False) → False) := by
  intro assump_37
  have assump_60 : ((((p3 → False) ∧ (p0 ∨ p3)) → ((p0 → False) ∧ (p5 ∧ p4))) → (((True ∧ p7) ∨ (p6 ∨ p1)) ∨ ((True → False) → (p3 ∧ p3)))) := by
    intro assump_41
    apply Or.inr
    intro assump_44
    apply And.intro
    have assump_61 : True := by
      apply True.intro
    let assump_47 := assump_44 assump_61
    apply False.elim assump_47
    have assump_62 : True := by
      apply True.intro
    let assump_53 := assump_44 assump_62
    apply False.elim assump_53
  let assump_40 := assump_37 assump_60
  apply False.elim assump_40


variable (p4 p2 p1 p6 p5 p7 p0 p3 : Prop)
theorem file21_2144 : (((((p0 → p0) ∨ (p7 ∨ False)) ∨ ((p5 → False) ∧ (p2 ∧ p2))) → (((p6 ∧ True) → (True ∨ p3)) ∨ ((p4 → False) → False))) ∨ ((((p1 → False) ∧ (p6 ∨ p3)) → ((p0 → False) → (p1 ∨ False))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_8
      cases assump_8
      case intro assump_9 assump_10 =>
        apply Or.inl
        apply True.intro
    case inr assump_5 =>
      cases assump_5
      case inl assump_15 =>
        apply Or.inl
        intro assump_19
        cases assump_19
        case intro assump_20 assump_21 =>
          apply Or.inl
          apply True.intro
      case inr assump_16 =>
        apply False.elim assump_16
  case inr assump_3 =>
    cases assump_3
    case intro assump_28 assump_29 =>
      cases assump_29
      case intro assump_32 assump_33 =>
        apply Or.inl
        intro assump_38
        cases assump_38
        case intro assump_39 assump_40 =>
          apply Or.inl
          apply True.intro


variable (p6 p0 p3 p7 p1 : Prop)
theorem file21_3262 : (((((p6 → p6) → False) → ((True → p7) → False)) ∨ (((p3 → False) → False) → ((p6 → p6) ∨ (False → True)))) ∨ ((((p3 → False) ∨ (p0 ∧ p0)) → False) → (((True → p3) → (p1 → p7)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_14 : (p6 → p6) := by
    intro assump_8
    exact assump_8
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7


variable (p5 p0 p7 p1 p3 p6 p4 p2 : Prop)
theorem file21_3723 : (((((p0 ∨ p3) → False) ∧ ((p2 → True) ∧ (p7 → False))) → (((True ∨ False) ∧ (p4 ∨ p1)) → ((p5 ∧ p1) → False))) → ((((p4 ∧ p5) → False) ∧ ((p2 ∧ p3) ∨ (True ∨ p6))) → (((p1 ∨ p5) → (p7 → False)) → ((p2 ∧ False) → (p4 ∧ p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6
  cases assump_4
  case intro assump_11 assump_12 =>
    apply False.elim assump_12


variable (p4 p5 p0 p6 p3 p7 : Prop)
theorem file21_4266 : (((((p0 → False) ∨ (p6 → False)) ∧ ((p0 → p6) ∨ (False → False))) ∧ (((p7 ∨ p5) ∧ (p4 → False)) ∧ ((p0 → p3) ∧ (True → False)))) → False) := by
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
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_16
              case inl assump_18 =>
                cases assump_15
                case intro assump_24 assump_25 =>
                  have assump_160 : True := by
                    apply True.intro
                  let assump_30 := assump_25 assump_160
                  apply False.elim assump_30
              case inr assump_19 =>
                cases assump_15
                case intro assump_38 assump_39 =>
                  have assump_161 : True := by
                    apply True.intro
                  let assump_44 := assump_39 assump_161
                  apply False.elim assump_44
        case inr assump_11 =>
          cases assump_3
          case intro assump_50 assump_51 =>
            cases assump_50
            case intro assump_52 assump_53 =>
              cases assump_52
              case inl assump_54 =>
                cases assump_51
                case intro assump_60 assump_61 =>
                  have assump_162 : True := by
                    apply True.intro
                  let assump_66 := assump_61 assump_162
                  apply False.elim assump_66
              case inr assump_55 =>
                cases assump_51
                case intro assump_74 assump_75 =>
                  have assump_163 : True := by
                    apply True.intro
                  let assump_80 := assump_75 assump_163
                  apply False.elim assump_80
      case inr assump_7 =>
        cases assump_5
        case inl assump_86 =>
          cases assump_3
          case intro assump_90 assump_91 =>
            cases assump_90
            case intro assump_92 assump_93 =>
              cases assump_92
              case inl assump_94 =>
                cases assump_91
                case intro assump_100 assump_101 =>
                  have assump_164 : True := by
                    apply True.intro
                  let assump_106 := assump_101 assump_164
                  apply False.elim assump_106
              case inr assump_95 =>
                cases assump_91
                case intro assump_114 assump_115 =>
                  have assump_165 : True := by
                    apply True.intro
                  let assump_120 := assump_115 assump_165
                  apply False.elim assump_120
        case inr assump_87 =>
          cases assump_3
          case intro assump_126 assump_127 =>
            cases assump_126
            case intro assump_128 assump_129 =>
              cases assump_128
              case inl assump_130 =>
                cases assump_127
                case intro assump_136 assump_137 =>
                  have assump_166 : True := by
                    apply True.intro
                  let assump_142 := assump_137 assump_166
                  apply False.elim assump_142
              case inr assump_131 =>
                cases assump_127
                case intro assump_150 assump_151 =>
                  have assump_167 : True := by
                    apply True.intro
                  let assump_156 := assump_151 assump_167
                  apply False.elim assump_156


variable (p5 p3 p0 p4 p1 p7 p6 : Prop)
theorem file21_7983 : (((((p7 ∧ p3) ∧ (False → p7)) ∧ ((p0 ∧ p1) → False)) → (((p7 → False) → (True ∧ p5)) ∨ ((False ∧ False) ∨ (p0 → p4)))) ∨ ((((p3 ∨ p6) → (True → False)) → False) → False)) := by
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
        apply And.intro
        apply True.intro
        have assump_23 : p7 := by
          exact assump_6
        let assump_19 := assump_16 assump_23
        apply False.elim assump_19


variable (p0 p3 p5 p1 p6 : Prop)
theorem file21_8647 : ((((((True → False) → (True → False)) ∨ ((True → False) ∨ (p0 ∧ False))) ∧ (((p6 ∨ p0) → (False → False)) ∨ ((p5 ∧ p1) → False))) ∧ ((((p0 → False) → (p6 ∨ True)) ∨ ((True ∨ True) ∧ (True ∧ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          have assump_68 : (((p0 → False) → (p6 ∨ True)) ∨ ((True ∨ True) ∧ (True ∧ p3))) := by
            apply Or.inl
            intro assump_17
            apply Or.inr
            apply True.intro
          let assump_16 := assump_3 assump_68
          apply False.elim assump_16
        case inr assump_11 =>
          have assump_69 : (((p0 → False) → (p6 ∨ True)) ∨ ((True ∨ True) ∧ (True ∧ p3))) := by
            apply Or.inl
            intro assump_28
            apply Or.inr
            apply True.intro
          let assump_27 := assump_3 assump_69
          apply False.elim assump_27
      case inr assump_7 =>
        cases assump_7
        case inl assump_34 =>
          cases assump_5
          case inl assump_38 =>
            have assump_70 : (((p0 → False) → (p6 ∨ True)) ∨ ((True ∨ True) ∧ (True ∧ p3))) := by
              apply Or.inl
              intro assump_45
              apply Or.inr
              apply True.intro
            let assump_44 := assump_3 assump_70
            apply False.elim assump_44
          case inr assump_39 =>
            have assump_71 : (((p0 → False) → (p6 ∨ True)) ∨ ((True ∨ True) ∧ (True ∧ p3))) := by
              apply Or.inl
              intro assump_56
              apply Or.inr
              apply True.intro
            let assump_55 := assump_3 assump_71
            apply False.elim assump_55
        case inr assump_35 =>
          cases assump_35
          case intro assump_62 assump_63 =>
            apply False.elim assump_63


variable (p6 p2 p7 p3 p1 : Prop)
theorem file21_10659 : (((((p7 ∨ True) → False) ∧ ((p6 ∨ p2) ∨ (p3 → False))) → False) ∧ ((((p6 ∨ p3) ∧ (False ∧ False)) → False) ∨ (((p7 ∨ False) ∧ (p7 ∧ p6)) ∧ ((p2 → p1) → False)))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        have assump_48 : (p7 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_13 := assump_2 assump_48
        apply False.elim assump_13
      case inr assump_9 =>
        have assump_49 : (p7 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_20 := assump_2 assump_49
        apply False.elim assump_20
    case inr assump_7 =>
      have assump_50 : (p7 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_27 := assump_2 assump_50
      apply False.elim assump_27
  apply Or.inl
  intro assump_31
  cases assump_31
  case intro assump_32 assump_33 =>
    cases assump_32
    case inl assump_34 =>
      cases assump_33
      case intro assump_38 assump_39 =>
        apply False.elim assump_38
    case inr assump_35 =>
      cases assump_33
      case intro assump_44 assump_45 =>
        apply False.elim assump_44


variable (p0 p4 p3 p7 p6 p1 p5 : Prop)
theorem file21_11979 : (((((p7 → False) → False) ∨ ((False → p7) ∨ (p4 ∨ p6))) ∧ (((p4 ∨ p5) → (p4 → False)) → False)) → ((((p3 ∧ False) ∧ (p7 ∨ False)) → ((p1 → p0) ∧ (p6 → False))) ∨ (((False → p7) ∨ (False → False)) ∨ ((False → p3) ∧ (p3 ∨ p0))))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      apply Or.inl
      intro assump_14
      apply And.intro
      intro assump_15
      cases assump_14
      case intro assump_18 assump_19 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          apply False.elim assump_21
      intro assump_26
      cases assump_14
      case intro assump_29 assump_30 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          apply False.elim assump_32
    case inr assump_9 =>
      cases assump_9
      case inl assump_37 =>
        apply Or.inl
        intro assump_43
        apply And.intro
        intro assump_44
        cases assump_43
        case intro assump_47 assump_48 =>
          cases assump_47
          case intro assump_49 assump_50 =>
            apply False.elim assump_50
        intro assump_55
        cases assump_43
        case intro assump_58 assump_59 =>
          cases assump_58
          case intro assump_60 assump_61 =>
            apply False.elim assump_61
      case inr assump_38 =>
        cases assump_38
        case inl assump_66 =>
          apply Or.inl
          intro assump_72
          apply And.intro
          intro assump_73
          cases assump_72
          case intro assump_76 assump_77 =>
            cases assump_76
            case intro assump_78 assump_79 =>
              apply False.elim assump_79
          intro assump_84
          cases assump_72
          case intro assump_87 assump_88 =>
            cases assump_87
            case intro assump_89 assump_90 =>
              apply False.elim assump_90
        case inr assump_67 =>
          apply Or.inl
          intro assump_99
          apply And.intro
          intro assump_100
          cases assump_99
          case intro assump_103 assump_104 =>
            cases assump_103
            case intro assump_105 assump_106 =>
              apply False.elim assump_106
          intro assump_111
          cases assump_99
          case intro assump_114 assump_115 =>
            cases assump_114
            case intro assump_116 assump_117 =>
              apply False.elim assump_117


variable (p6 p3 p7 p5 : Prop)
theorem file21_14477 : ((((((p3 → False) → (p6 → False)) ∨ ((False ∨ p7) ∨ (p5 → False))) → (((p7 → p7) ∨ (p7 ∧ p5)) ∨ ((p5 ∨ p5) ∧ (p5 ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p3 → False) → (p6 → False)) ∨ ((False ∨ p7) ∨ (p5 → False))) → (((p7 → p7) ∨ (p7 ∧ p5)) ∨ ((p5 ∨ p5) ∧ (p5 ∧ p5)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply Or.inl
      intro assump_10
      exact assump_10
    case inr assump_7 =>
      cases assump_7
      case inl assump_13 =>
        cases assump_13
        case inl assump_15 =>
          apply False.elim assump_15
        case inr assump_16 =>
          apply Or.inl
          apply Or.inl
          intro assump_21
          exact assump_21
      case inr assump_14 =>
        apply Or.inl
        apply Or.inl
        intro assump_26
        exact assump_26
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p6 p5 p0 p1 : Prop)
theorem file21_15460 : (((((p5 ∧ p0) → False) ∨ ((p6 → p6) → False)) ∧ (((p5 ∧ p1) → (p1 ∨ p5)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_36 : ((p5 ∧ p1) → (p1 ∨ p5)) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          apply Or.inl
          exact assump_13
      let assump_10 := assump_3 assump_36
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_37 : ((p5 ∧ p1) → (p1 ∨ p5)) := by
        intro assump_26
        cases assump_26
        case intro assump_27 assump_28 =>
          apply Or.inl
          exact assump_28
      let assump_25 := assump_3 assump_37
      apply False.elim assump_25


variable (p6 p2 p1 p7 p0 p3 p5 : Prop)
theorem file21_16292 : (((((p2 ∧ p3) ∨ (False → False)) ∨ ((p5 ∨ p0) ∧ (True ∧ p5))) ∨ (((p5 ∨ p3) ∨ (p5 → False)) → ((True ∧ False) → (p7 ∧ True)))) ∨ ((((True ∨ p2) → (p5 → p0)) ∨ ((p3 → False) → (p3 ∨ p0))) ∧ (((True ∨ p3) ∧ (p1 → False)) → ((p6 → False) ∨ (True → p3))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply False.elim assump_1


variable (p2 p1 p7 p4 p3 : Prop)
theorem file21_16713 : ((((((False → False) ∧ (p3 ∨ p2)) → ((p7 ∧ False) → (p4 ∨ p1))) ∨ (((p2 → False) → (p4 → False)) → False)) → False) → False) := by
  intro assump_33
  have assump_48 : ((((False → False) ∧ (p3 ∨ p2)) → ((p7 ∧ False) → (p4 ∨ p1))) ∨ (((p2 → False) → (p4 → False)) → False)) := by
    apply Or.inl
    intro assump_37
    intro assump_38
    cases assump_38
    case intro assump_39 assump_40 =>
      apply False.elim assump_40
  let assump_36 := assump_33 assump_48
  apply False.elim assump_36


variable (p5 p6 p0 p1 p4 p2 p7 p3 : Prop)
theorem file21_17274 : (((((p1 ∨ p0) ∧ (p5 ∨ p0)) → ((p5 → p5) → (p5 → False))) → (((p6 ∨ p4) → (p0 ∧ False)) ∧ ((p1 ∨ p7) → (p1 → False)))) → ((((False ∨ True) ∧ (p1 ∨ p1)) ∧ ((p0 ∨ p0) ∨ (p3 ∧ p6))) ∨ (((p4 ∧ p2) ∨ (False → False)) ∨ ((True → p6) → (True ∧ p7))))) := by
  intro assump_1
  apply Or.inr
  apply Or.inl
  apply Or.inr
  intro assump_4
  apply False.elim assump_4


theorem file21_17655 : (((((True → False) → False) ∨ ((False → True) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : (((True → False) → False) ∨ ((False → True) → False)) := by
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p2 p3 p4 p5 p0 : Prop)
theorem file21_18116 : (((((p2 → False) → False) ∨ ((p0 → False) → False)) → False) → ((((p5 → p0) → (False ∧ p3)) ∧ ((p6 → False) ∧ (p4 ∧ p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        have assump_30 : (((p2 → False) → False) ∨ ((p0 → False) → False)) := by
          apply Or.inl
          intro assump_20
          have assump_31 : p2 := by
            exact assump_12
          let assump_23 := assump_20 assump_31
          apply False.elim assump_23
        let assump_19 := assump_1 assump_30
        apply False.elim assump_19


variable (p7 p5 p2 p4 p1 p3 : Prop)
theorem file21_18872 : ((((((True ∨ p5) → False) → False) ∨ (((p2 → False) ∧ (p1 ∨ p7)) → ((p3 ∨ False) → (p4 ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ p5) → False) → False) ∨ (((p2 → False) ∧ (p1 ∨ p7)) → ((p3 ∨ False) → (p4 ∨ p5)))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (True ∨ p5) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p4 p0 p3 : Prop)
theorem file21_19433 : ((((((p6 ∨ p4) → (p3 ∨ True)) → False) → False) → ((((p0 → True) ∨ (False → p0)) → False) ∧ (((p6 → False) ∧ (True ∧ p3)) ∧ ((p6 → False) → False)))) → False) := by
  intro assump_1
  have assump_25 : ((((p6 ∨ p4) → (p3 ∨ True)) → False) → False) := by
    intro assump_5
    have assump_26 : ((p6 ∨ p4) → (p3 ∨ True)) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inr
        apply True.intro
      case inr assump_11 =>
        apply Or.inr
        apply True.intro
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  let assump_19 := And.left assump_4
  have assump_27 : ((p0 → True) ∨ (False → p0)) := by
    apply Or.inl
    intro assump_21
    apply True.intro
  let assump_20 := assump_19 assump_27
  apply False.elim assump_20


variable (p7 p5 p0 p3 p1 p6 p4 p2 : Prop)
theorem file21_20337 : (((((p2 → p7) → (p3 ∨ True)) ∨ ((p1 → p3) → (p4 ∧ p4))) → (((p2 ∧ p5) ∧ (p3 ∨ p4)) → ((p1 → False) → (p3 ∨ p5)))) → ((((p2 → p2) ∨ (p0 ∨ p2)) → False) → (((p4 ∧ p6) ∨ (p0 ∨ False)) ∧ ((p0 → False) ∧ (p0 → True))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  have assump_39 : ((p2 → p2) ∨ (p0 ∨ p2)) := by
    apply Or.inl
    intro assump_13
    exact assump_13
  let assump_12 := assump_2 assump_39
  apply False.elim assump_12
  apply And.intro
  intro assump_19
  have assump_40 : ((p2 → p2) ∨ (p0 ∨ p2)) := by
    apply Or.inl
    intro assump_32
    exact assump_32
  let assump_31 := assump_2 assump_40
  apply False.elim assump_31
  intro assump_38
  apply True.intro


variable (p6 p3 p5 p1 p0 p4 : Prop)
theorem file21_21089 : (((((True → p1) → False) → ((p5 → False) → (p3 ∨ True))) → False) → ((((p4 ∨ p4) ∨ (p6 → False)) ∧ ((p0 ∧ p1) → (p0 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        have assump_57 : (((True → p1) → False) → ((p5 → False) → (p3 ∨ True))) := by
          intro assump_16
          intro assump_17
          apply Or.inr
          apply True.intro
        let assump_15 := assump_1 assump_57
        apply False.elim assump_15
      case inr assump_8 =>
        have assump_58 : (((True → p1) → False) → ((p5 → False) → (p3 ∨ True))) := by
          intro assump_32
          intro assump_33
          apply Or.inr
          apply True.intro
        let assump_31 := assump_1 assump_58
        apply False.elim assump_31
    case inr assump_6 =>
      have assump_59 : (((True → p1) → False) → ((p5 → False) → (p3 ∨ True))) := by
        intro assump_48
        intro assump_49
        apply Or.inr
        apply True.intro
      let assump_47 := assump_1 assump_59
      apply False.elim assump_47


variable (p4 p7 p6 p0 p3 p5 : Prop)
theorem file21_22308 : (((((False → p3) → False) ∧ ((False ∨ p7) → False)) → False) ∨ ((((p4 → p5) ∧ (False ∧ p5)) ∧ ((p3 → False) → False)) → (((p0 ∨ True) ∨ (p6 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (False → p3) := by
      intro assump_10
      apply False.elim assump_10
    let assump_9 := assump_2 assump_16
    apply False.elim assump_9


variable (p0 p1 p7 p4 p5 p6 : Prop)
theorem file21_22782 : (((((p6 → True) → False) → ((p7 → True) → False)) ∨ (((p7 → p1) → False) ∧ ((p0 ∨ True) ∧ (p4 ∧ p5)))) ∨ ((((p1 ∨ p5) → False) → ((False ∨ p6) ∧ (p1 ∨ p5))) → (((p6 → False) → (True ∨ True)) → ((p5 ∨ p0) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_12 : (p6 → True) := by
    intro assump_8
    apply True.intro
  let assump_7 := assump_1 assump_12
  apply False.elim assump_7


variable (p5 p7 p6 p4 p0 p1 p2 : Prop)
theorem file21_23273 : (((((True → False) → False) → False) → (((p7 → p4) → False) → ((p7 ∨ p7) → (p5 ∧ p2)))) ∨ ((((False → p1) → False) → ((p5 → False) → (p7 ∧ p1))) ∨ (((p1 ∧ p4) ∧ (True ∨ p4)) → ((p4 → p0) ∨ (p5 ∨ p6))))) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  intro assump_7
  apply And.intro
  cases assump_7
  case inl assump_8 =>
    have assump_80 : ((True → False) → False) := by
      intro assump_17
      have assump_81 : True := by
        apply True.intro
      let assump_20 := assump_17 assump_81
      apply False.elim assump_20
    let assump_16 := assump_5 assump_80
    apply False.elim assump_16
  case inr assump_9 =>
    have assump_82 : ((True → False) → False) := by
      intro assump_34
      have assump_83 : True := by
        apply True.intro
      let assump_37 := assump_34 assump_83
      apply False.elim assump_37
    let assump_33 := assump_5 assump_82
    apply False.elim assump_33
  cases assump_7
  case inl assump_44 =>
    have assump_84 : ((True → False) → False) := by
      intro assump_53
      have assump_85 : True := by
        apply True.intro
      let assump_56 := assump_53 assump_85
      apply False.elim assump_56
    let assump_52 := assump_5 assump_84
    apply False.elim assump_52
  case inr assump_45 =>
    have assump_86 : ((True → False) → False) := by
      intro assump_70
      have assump_87 : True := by
        apply True.intro
      let assump_73 := assump_70 assump_87
      apply False.elim assump_73
    let assump_69 := assump_5 assump_86
    apply False.elim assump_69


variable (p5 p3 : Prop)
theorem file21_24862 : ((((((False ∨ p5) ∨ (False → True)) → False) → (((p3 → False) ∨ (True ∨ p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_41 : ((((False ∨ p5) ∨ (False → True)) → False) → (((p3 → False) ∨ (True ∨ p3)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_42 : ((False ∨ p5) ∨ (False → True)) := by
        apply Or.inr
        intro assump_14
        apply True.intro
      let assump_13 := assump_5 assump_42
      apply False.elim assump_13
    case inr assump_8 =>
      cases assump_8
      case inl assump_18 =>
        have assump_43 : ((False ∨ p5) ∨ (False → True)) := by
          apply Or.inr
          intro assump_25
          apply True.intro
        let assump_24 := assump_5 assump_43
        apply False.elim assump_24
      case inr assump_19 =>
        have assump_44 : ((False ∨ p5) ∨ (False → True)) := by
          apply Or.inr
          intro assump_34
          apply True.intro
        let assump_33 := assump_5 assump_44
        apply False.elim assump_33
  let assump_4 := assump_1 assump_41
  apply False.elim assump_4


variable (p6 p5 p1 p3 p2 p4 p0 p7 : Prop)
theorem file21_26057 : ((((((p1 ∧ p2) ∧ (p7 → False)) ∨ ((p5 → False) ∧ (p5 ∨ p3))) ∧ (((p0 ∧ p7) ∧ (p3 ∧ True)) → ((p3 ∧ p6) ∧ (p3 ∧ p7)))) ∧ ((((p2 → p4) → (p7 ∧ p2)) → ((p6 ∨ p1) → (p5 → False))) ∧ (((True ∨ p0) → (p3 → True)) → False))) → False) := by
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_20
      case inl assump_22 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            cases assump_19
            case intro assump_36 assump_37 =>
              have assump_86 : ((True ∨ p0) → (p3 → True)) := by
                intro assump_43
                intro assump_44
                apply True.intro
              let assump_42 := assump_37 assump_86
              apply False.elim assump_42
      case inr assump_23 =>
        cases assump_23
        case intro assump_48 assump_49 =>
          cases assump_49
          case inl assump_52 =>
            cases assump_19
            case intro assump_58 assump_59 =>
              have assump_87 : ((True ∨ p0) → (p3 → True)) := by
                intro assump_65
                intro assump_66
                apply True.intro
              let assump_64 := assump_59 assump_87
              apply False.elim assump_64
          case inr assump_53 =>
            cases assump_19
            case intro assump_74 assump_75 =>
              have assump_88 : ((True ∨ p0) → (p3 → True)) := by
                intro assump_81
                intro assump_82
                apply True.intro
              let assump_80 := assump_75 assump_88
              apply False.elim assump_80


variable (p6 p7 p0 p3 p1 p4 p5 : Prop)
theorem file21_27837 : (((((False ∧ p3) ∧ (True → p7)) ∧ ((p1 ∧ p6) → (p3 ∨ p1))) ∧ (((p4 ∨ False) ∧ (p5 → True)) ∧ ((p4 → False) → (p5 → p0)))) → ((((True ∧ True) ∨ (p4 ∧ p3)) ∧ ((p5 → False) ∧ (p7 ∨ p7))) ∨ (((p4 → False) → False) → False))) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          apply False.elim assump_16


variable (p1 p5 p4 p0 p3 p6 p7 : Prop)
theorem file21_28420 : ((((((p3 → False) ∨ (p4 ∨ p6)) → False) → (((p6 ∨ p3) ∨ (p3 → False)) ∨ ((p5 → p7) ∧ (p0 → p7)))) ∧ ((((p1 ∨ False) → False) → ((p1 ∧ False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((p1 ∨ False) → False) → ((p1 ∧ False) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p5 p7 p2 p6 p1 p3 p4 : Prop)
theorem file21_29013 : (((((False → False) ∨ (p4 ∨ p1)) → ((p5 ∨ p5) → (p7 → p5))) ∨ (((p3 → True) → (False → p7)) → False)) ∨ ((((p4 ∧ p7) → False) → False) ∧ (((p2 ∨ p5) ∧ (p6 ∨ p1)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_1
    case inl assump_10 =>
      exact assump_6
    case inr assump_11 =>
      cases assump_11
      case inl assump_14 =>
        exact assump_6
      case inr assump_15 =>
        exact assump_6
  case inr assump_7 =>
    cases assump_1
    case inl assump_22 =>
      exact assump_7
    case inr assump_23 =>
      cases assump_23
      case inl assump_26 =>
        exact assump_7
      case inr assump_27 =>
        exact assump_7


variable (p0 p4 p7 p3 p2 p1 p5 : Prop)
theorem file21_29831 : (((((False ∨ False) → False) ∨ ((p1 ∧ p5) ∨ (p7 ∨ p0))) ∨ (((p2 → False) → False) ∧ ((p3 → False) → (p4 → False)))) → ((((p7 ∨ p5) ∧ (True ∨ p4)) ∨ ((True → False) ∨ (p1 → False))) → (((True → p4) ∧ (p3 ∨ p2)) → ((p2 ∧ False) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p2 p0 p7 p3 p1 p6 : Prop)
theorem file21_30284 : (((((p1 → p1) → False) → ((p0 → False) → (p1 → False))) ∨ (((p0 → p0) → (p0 → p0)) → ((p1 ∨ False) ∨ (False ∨ False)))) ∨ ((((p2 ∧ p7) → False) → False) → (((p1 ∨ p0) → (p6 → False)) ∨ ((p3 → False) ∧ (False ∨ p2))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_17 : (p1 → p1) := by
    intro assump_11
    exact assump_11
  let assump_10 := assump_1 assump_17
  apply False.elim assump_10


variable (p1 p4 p0 p6 p7 p5 p3 : Prop)
theorem file21_30794 : (((((p6 ∨ False) ∧ (p1 → p1)) → False) ∧ (((p1 → p4) → False) ∨ ((p5 ∧ p1) → False))) → ((((True → p0) ∨ (p3 → False)) ∧ ((False ∧ p5) ∧ (p0 ∧ p7))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          apply False.elim assump_11
    case inr assump_6 =>
      cases assump_4
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          apply False.elim assump_19


variable (p7 p0 p6 p3 p1 p4 p2 : Prop)
theorem file21_31502 : (((((p4 → False) → False) ∧ ((p0 → False) ∧ (True → False))) → False) ∨ ((((p1 ∧ p0) ∧ (p3 ∧ p4)) ∨ ((False → p7) ∨ (p2 ∧ True))) ∧ (((p7 → True) ∨ (p6 ∧ p2)) → ((p0 ∧ p4) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_16 : True := by
        apply True.intro
      let assump_12 := assump_7 assump_16
      apply False.elim assump_12


variable (p7 p3 p4 p2 p5 p1 p6 p0 : Prop)
theorem file21_32030 : (((((p3 → p2) → (p6 ∧ p4)) → False) ∧ (((p0 → False) → False) ∧ ((p5 → p5) ∧ (p1 ∧ p6)))) → ((((p2 → p1) → False) → False) ∨ (((p3 → False) → False) ∨ ((p7 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply Or.inl
          intro assump_20
          have assump_30 : (p2 → p1) := by
            intro assump_24
            exact assump_14
          let assump_23 := assump_20 assump_30
          apply False.elim assump_23


variable (p4 p5 p0 p3 : Prop)
theorem file21_32749 : ((((((p5 → p0) → False) ∧ ((True → True) → False)) → (((p4 → False) ∧ (p3 → p5)) ∧ ((True ∨ p0) → False))) → False) → False) := by
  intro assump_1
  have assump_66 : ((((p5 → p0) → False) ∧ ((True → True) → False)) → (((p4 → False) ∧ (p3 → p5)) ∧ ((True ∨ p0) → False))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      have assump_67 : (True → True) := by
        intro assump_16
        apply True.intro
      let assump_15 := assump_10 assump_67
      apply False.elim assump_15
    intro assump_20
    cases assump_5
    case intro assump_23 assump_24 =>
      have assump_68 : (True → True) := by
        intro assump_30
        apply True.intro
      let assump_29 := assump_24 assump_68
      apply False.elim assump_29
    intro assump_34
    cases assump_34
    case inl assump_35 =>
      cases assump_5
      case intro assump_39 assump_40 =>
        have assump_69 : (True → True) := by
          intro assump_46
          apply True.intro
        let assump_45 := assump_40 assump_69
        apply False.elim assump_45
    case inr assump_36 =>
      cases assump_5
      case intro assump_52 assump_53 =>
        have assump_70 : (True → True) := by
          intro assump_59
          apply True.intro
        let assump_58 := assump_53 assump_70
        apply False.elim assump_58
  let assump_4 := assump_1 assump_66
  apply False.elim assump_4


variable (p4 p5 p2 p3 p6 : Prop)
theorem file21_34266 : ((((((p3 → False) ∨ (p5 ∨ p6)) → ((False → p4) ∧ (True → False))) → (((p4 ∨ False) ∨ (p2 → True)) ∨ ((False ∨ p6) → False))) → False) → False) := by
  intro assump_17
  have assump_28 : ((((p3 → False) ∨ (p5 ∨ p6)) → ((False → p4) ∧ (True → False))) → (((p4 ∨ False) ∨ (p2 → True)) ∨ ((False ∨ p6) → False))) := by
    intro assump_21
    apply Or.inl
    apply Or.inr
    intro assump_24
    apply True.intro
  let assump_20 := assump_17 assump_28
  apply False.elim assump_20


variable (p3 p4 p6 p7 p0 p1 p2 : Prop)
theorem file21_34807 : ((((((p1 → False) → (p6 ∨ p2)) ∧ ((p6 ∧ p6) → (p7 → False))) → False) ∧ ((((False ∧ p2) → (p4 ∧ p4)) → ((p3 → False) → (p0 ∧ True))) ∧ (((p3 → False) ∧ (p7 ∧ p3)) ∧ ((p7 → False) ∨ (p1 ∧ p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_11
            case inl assump_22 =>
              have assump_44 : p7 := by
                exact assump_16
              let assump_26 := assump_22 assump_44
              apply False.elim assump_26
            case inr assump_23 =>
              cases assump_23
              case intro assump_30 assump_31 =>
                have assump_45 : p3 := by
                  exact assump_31
                let assump_40 := assump_12 assump_45
                apply False.elim assump_40


variable (p4 p3 p0 : Prop)
theorem file21_35898 : ((((((p0 → False) ∨ (p3 → p4)) ∧ ((True ∨ True) → False)) → False) → False) → False) := by
  intro assump_4
  have assump_32 : ((((p0 → False) ∨ (p3 → p4)) ∧ ((True ∨ True) → False)) → False) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        have assump_33 : (True ∨ True) := by
          apply Or.inl
          apply True.intro
        let assump_17 := assump_10 assump_33
        apply False.elim assump_17
      case inr assump_12 =>
        have assump_34 : (True ∨ True) := by
          apply Or.inl
          apply True.intro
        let assump_25 := assump_10 assump_34
        apply False.elim assump_25
  let assump_7 := assump_4 assump_32
  apply False.elim assump_7


variable (p2 p5 p1 p0 p7 p3 p4 p6 : Prop)
theorem file21_36729 : (((((p5 ∧ p2) ∨ (p6 ∧ p4)) ∨ ((p5 ∧ p4) ∧ (p2 → p2))) → (((p2 ∧ p3) ∨ (p7 ∨ p3)) → ((p7 ∧ p0) ∨ (p5 ∨ p6)))) ∨ ((((p6 ∨ True) ∧ (True ∨ p5)) → False) ∨ (((True → p3) ∧ (p5 → False)) ∧ ((p6 ∧ p2) → (p1 → False))))) := by
  apply Or.inl
  intro assump_13
  intro assump_14
  cases assump_14
  case inl assump_15 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_13
      case inl assump_23 =>
        cases assump_23
        case inl assump_25 =>
          cases assump_25
          case intro assump_27 assump_28 =>
            apply Or.inr
            apply Or.inl
            exact assump_27
        case inr assump_26 =>
          cases assump_26
          case intro assump_33 assump_34 =>
            apply Or.inr
            apply Or.inr
            exact assump_33
      case inr assump_24 =>
        cases assump_24
        case intro assump_39 assump_40 =>
          cases assump_39
          case intro assump_41 assump_42 =>
            apply Or.inr
            apply Or.inl
            exact assump_41
  case inr assump_16 =>
    cases assump_16
    case inl assump_49 =>
      cases assump_13
      case inl assump_53 =>
        cases assump_53
        case inl assump_55 =>
          cases assump_55
          case intro assump_57 assump_58 =>
            apply Or.inr
            apply Or.inl
            exact assump_57
        case inr assump_56 =>
          cases assump_56
          case intro assump_63 assump_64 =>
            apply Or.inr
            apply Or.inr
            exact assump_63
      case inr assump_54 =>
        cases assump_54
        case intro assump_69 assump_70 =>
          cases assump_69
          case intro assump_71 assump_72 =>
            apply Or.inr
            apply Or.inl
            exact assump_71
    case inr assump_50 =>
      cases assump_13
      case inl assump_81 =>
        cases assump_81
        case inl assump_83 =>
          cases assump_83
          case intro assump_85 assump_86 =>
            apply Or.inr
            apply Or.inl
            exact assump_85
        case inr assump_84 =>
          cases assump_84
          case intro assump_91 assump_92 =>
            apply Or.inr
            apply Or.inr
            exact assump_91
      case inr assump_82 =>
        cases assump_82
        case intro assump_97 assump_98 =>
          cases assump_97
          case intro assump_99 assump_100 =>
            apply Or.inr
            apply Or.inl
            exact assump_99


variable (p7 p1 p3 p5 p2 p4 : Prop)
theorem file21_39273 : (((((p3 → False) → (p7 ∨ p7)) → False) → (((False ∨ p4) → False) ∧ ((p7 ∨ True) ∧ (p3 ∨ p1)))) → ((((p2 → False) ∨ (p1 → False)) ∧ ((p2 → p2) → (True → False))) → (((p5 → p5) ∨ (p1 → False)) ∨ ((p1 ∨ p4) ∨ (p1 ∧ False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      apply Or.inl
      apply Or.inl
      intro assump_13
      exact assump_13
    case inr assump_6 =>
      apply Or.inl
      apply Or.inl
      intro assump_22
      exact assump_22


variable (p0 p2 p1 p3 p4 p6 : Prop)
theorem file21_39880 : (((((False → p6) ∨ (p0 → False)) → ((True → False) ∧ (p0 → False))) → (((p4 → False) → (p2 ∨ p0)) ∨ ((p2 ∨ p4) ∧ (p1 ∨ p0)))) ∨ ((((p4 → False) ∧ (True ∧ p4)) ∨ ((p2 ∧ p3) → (p4 → True))) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_17 : ((False → p6) ∨ (p0 → False)) := by
    apply Or.inl
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_1 assump_17
  let assump_12 := And.left assump_8
  have assump_18 : True := by
    apply True.intro
  let assump_13 := assump_12 assump_18
  apply False.elim assump_13


variable (p2 p5 p3 p7 p1 p6 : Prop)
theorem file21_40522 : (((((True → p2) ∧ (p3 ∧ p3)) → ((p6 → p5) → False)) ∨ (((p1 ∨ p7) ∧ (False → False)) ∨ ((p2 ∨ p7) ∧ (p2 ∧ p3)))) → ((((p6 ∧ False) ∧ (p2 → False)) ∧ ((p6 ∨ False) → (p6 ∧ p1))) → (((False → True) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        apply False.elim assump_11


variable (p1 p2 p5 p0 p7 : Prop)
theorem file21_41054 : ((((((p7 ∧ p2) ∨ (p0 → False)) → ((True ∨ p5) ∨ (p7 ∧ False))) ∨ (((False ∨ False) ∧ (True ∨ p1)) ∨ ((p7 ∧ p7) ∧ (p7 ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p7 ∧ p2) ∨ (p0 → False)) → ((True ∨ p5) ∨ (p7 ∧ False))) ∨ (((False ∨ False) ∧ (True ∨ p1)) ∨ ((p7 ∧ p7) ∧ (p7 ∧ p5)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
    case inr assump_7 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p6 p2 p1 p0 p4 : Prop)
theorem file21_41784 : ((((((p1 → p6) ∨ (p2 ∨ p0)) → False) → (((p4 ∧ p6) → (True → p1)) ∧ ((p6 ∨ p6) → False))) → False) → False) := by
  intro assump_1
  have assump_53 : ((((p1 → p6) ∨ (p2 ∨ p0)) → False) → (((p4 ∧ p6) → (True → p1)) ∧ ((p6 ∨ p6) → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      have assump_54 : ((p1 → p6) ∨ (p2 ∨ p0)) := by
        apply Or.inl
        intro assump_19
        exact assump_11
      let assump_18 := assump_5 assump_54
      apply False.elim assump_18
    intro assump_25
    cases assump_25
    case inl assump_26 =>
      have assump_55 : ((p1 → p6) ∨ (p2 ∨ p0)) := by
        apply Or.inl
        intro assump_33
        exact assump_26
      let assump_32 := assump_5 assump_55
      apply False.elim assump_32
    case inr assump_27 =>
      have assump_56 : ((p1 → p6) ∨ (p2 ∨ p0)) := by
        apply Or.inl
        intro assump_44
        exact assump_27
      let assump_43 := assump_5 assump_56
      apply False.elim assump_43
  let assump_4 := assump_1 assump_53
  apply False.elim assump_4


variable (p5 p1 p0 p6 p7 p3 p4 : Prop)
theorem file21_42973 : ((((((p4 → True) ∨ (p0 ∨ p7)) ∨ ((p7 → False) → False)) → False) ∧ ((((p4 ∧ p1) ∧ (p4 → p6)) → ((True → p6) ∧ (p5 ∨ p3))) ∨ (((p1 ∧ False) ∧ (p7 ∧ p6)) ∧ ((p3 ∧ p6) → False)))) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_13
    case inl assump_16 =>
      have assump_36 : (((p4 → True) ∨ (p0 ∨ p7)) ∨ ((p7 → False) → False)) := by
        apply Or.inl
        apply Or.inl
        intro assump_22
        apply True.intro
      let assump_21 := assump_12 assump_36
      apply False.elim assump_21
    case inr assump_17 =>
      cases assump_17
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          cases assump_28
          case intro assump_30 assump_31 =>
            apply False.elim assump_31


variable (p7 p6 p0 p5 p2 p1 p3 p4 : Prop)
theorem file21_43861 : (((((False ∨ p6) ∨ (p3 ∧ p2)) ∧ ((True ∧ p2) → False)) ∧ (((False → False) ∨ (p2 ∧ p1)) → False)) → ((((p7 ∨ p5) ∨ (True ∨ p0)) ∨ ((p0 ∧ p5) ∨ (p4 → False))) → (((p2 → False) → (p4 → p6)) ∧ ((p3 ∨ p0) ∧ (p2 ∧ p4))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  intro assump_4
  cases assump_2
  case inl assump_9 =>
    cases assump_9
    case inl assump_11 =>
      cases assump_11
      case inl assump_13 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              cases assump_21
              case inl assump_23 =>
                apply False.elim assump_23
              case inr assump_24 =>
                exact assump_24
            case inr assump_22 =>
              cases assump_22
              case intro assump_33 assump_34 =>
                have assump_933 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_44
                  apply False.elim assump_44
                let assump_43 := assump_18 assump_933
                apply False.elim assump_43
      case inr assump_14 =>
        cases assump_1
        case intro assump_52 assump_53 =>
          cases assump_52
          case intro assump_54 assump_55 =>
            cases assump_54
            case inl assump_56 =>
              cases assump_56
              case inl assump_58 =>
                apply False.elim assump_58
              case inr assump_59 =>
                exact assump_59
            case inr assump_57 =>
              cases assump_57
              case intro assump_68 assump_69 =>
                have assump_934 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_79
                  apply False.elim assump_79
                let assump_78 := assump_53 assump_934
                apply False.elim assump_78
    case inr assump_12 =>
      cases assump_12
      case inl assump_85 =>
        cases assump_1
        case intro assump_89 assump_90 =>
          cases assump_89
          case intro assump_91 assump_92 =>
            cases assump_91
            case inl assump_93 =>
              cases assump_93
              case inl assump_95 =>
                apply False.elim assump_95
              case inr assump_96 =>
                exact assump_96
            case inr assump_94 =>
              cases assump_94
              case intro assump_105 assump_106 =>
                have assump_935 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_116
                  apply False.elim assump_116
                let assump_115 := assump_90 assump_935
                apply False.elim assump_115
      case inr assump_86 =>
        cases assump_1
        case intro assump_124 assump_125 =>
          cases assump_124
          case intro assump_126 assump_127 =>
            cases assump_126
            case inl assump_128 =>
              cases assump_128
              case inl assump_130 =>
                apply False.elim assump_130
              case inr assump_131 =>
                exact assump_131
            case inr assump_129 =>
              cases assump_129
              case intro assump_140 assump_141 =>
                have assump_936 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_151
                  apply False.elim assump_151
                let assump_150 := assump_125 assump_936
                apply False.elim assump_150
  case inr assump_10 =>
    cases assump_10
    case inl assump_157 =>
      cases assump_157
      case intro assump_159 assump_160 =>
        cases assump_1
        case intro assump_165 assump_166 =>
          cases assump_165
          case intro assump_167 assump_168 =>
            cases assump_167
            case inl assump_169 =>
              cases assump_169
              case inl assump_171 =>
                apply False.elim assump_171
              case inr assump_172 =>
                exact assump_172
            case inr assump_170 =>
              cases assump_170
              case intro assump_181 assump_182 =>
                have assump_937 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_192
                  apply False.elim assump_192
                let assump_191 := assump_166 assump_937
                apply False.elim assump_191
    case inr assump_158 =>
      cases assump_1
      case intro assump_200 assump_201 =>
        cases assump_200
        case intro assump_202 assump_203 =>
          cases assump_202
          case inl assump_204 =>
            cases assump_204
            case inl assump_206 =>
              apply False.elim assump_206
            case inr assump_207 =>
              exact assump_207
          case inr assump_205 =>
            cases assump_205
            case intro assump_216 assump_217 =>
              have assump_938 : ((False → False) ∨ (p2 ∧ p1)) := by
                apply Or.inl
                intro assump_227
                apply False.elim assump_227
              let assump_226 := assump_201 assump_938
              apply False.elim assump_226
  apply And.intro
  cases assump_2
  case inl assump_233 =>
    cases assump_233
    case inl assump_235 =>
      cases assump_235
      case inl assump_237 =>
        cases assump_1
        case intro assump_241 assump_242 =>
          cases assump_241
          case intro assump_243 assump_244 =>
            cases assump_243
            case inl assump_245 =>
              cases assump_245
              case inl assump_247 =>
                apply False.elim assump_247
              case inr assump_248 =>
                have assump_939 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_258
                  apply False.elim assump_258
                let assump_257 := assump_242 assump_939
                apply False.elim assump_257
            case inr assump_246 =>
              cases assump_246
              case intro assump_264 assump_265 =>
                apply Or.inl
                exact assump_264
      case inr assump_238 =>
        cases assump_1
        case intro assump_276 assump_277 =>
          cases assump_276
          case intro assump_278 assump_279 =>
            cases assump_278
            case inl assump_280 =>
              cases assump_280
              case inl assump_282 =>
                apply False.elim assump_282
              case inr assump_283 =>
                have assump_940 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_293
                  apply False.elim assump_293
                let assump_292 := assump_277 assump_940
                apply False.elim assump_292
            case inr assump_281 =>
              cases assump_281
              case intro assump_299 assump_300 =>
                apply Or.inl
                exact assump_299
    case inr assump_236 =>
      cases assump_236
      case inl assump_309 =>
        cases assump_1
        case intro assump_313 assump_314 =>
          cases assump_313
          case intro assump_315 assump_316 =>
            cases assump_315
            case inl assump_317 =>
              cases assump_317
              case inl assump_319 =>
                apply False.elim assump_319
              case inr assump_320 =>
                have assump_941 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_330
                  apply False.elim assump_330
                let assump_329 := assump_314 assump_941
                apply False.elim assump_329
            case inr assump_318 =>
              cases assump_318
              case intro assump_336 assump_337 =>
                apply Or.inl
                exact assump_336
      case inr assump_310 =>
        cases assump_1
        case intro assump_348 assump_349 =>
          cases assump_348
          case intro assump_350 assump_351 =>
            cases assump_350
            case inl assump_352 =>
              cases assump_352
              case inl assump_354 =>
                apply False.elim assump_354
              case inr assump_355 =>
                apply Or.inr
                exact assump_310
            case inr assump_353 =>
              cases assump_353
              case intro assump_364 assump_365 =>
                apply Or.inl
                exact assump_364
  case inr assump_234 =>
    cases assump_234
    case inl assump_374 =>
      cases assump_374
      case intro assump_376 assump_377 =>
        cases assump_1
        case intro assump_382 assump_383 =>
          cases assump_382
          case intro assump_384 assump_385 =>
            cases assump_384
            case inl assump_386 =>
              cases assump_386
              case inl assump_388 =>
                apply False.elim assump_388
              case inr assump_389 =>
                apply Or.inr
                exact assump_376
            case inr assump_387 =>
              cases assump_387
              case intro assump_398 assump_399 =>
                apply Or.inl
                exact assump_398
    case inr assump_375 =>
      cases assump_1
      case intro assump_410 assump_411 =>
        cases assump_410
        case intro assump_412 assump_413 =>
          cases assump_412
          case inl assump_414 =>
            cases assump_414
            case inl assump_416 =>
              apply False.elim assump_416
            case inr assump_417 =>
              have assump_942 : ((False → False) ∨ (p2 ∧ p1)) := by
                apply Or.inl
                intro assump_427
                apply False.elim assump_427
              let assump_426 := assump_411 assump_942
              apply False.elim assump_426
          case inr assump_415 =>
            cases assump_415
            case intro assump_433 assump_434 =>
              apply Or.inl
              exact assump_433
  apply And.intro
  cases assump_2
  case inl assump_443 =>
    cases assump_443
    case inl assump_445 =>
      cases assump_445
      case inl assump_447 =>
        cases assump_1
        case intro assump_451 assump_452 =>
          cases assump_451
          case intro assump_453 assump_454 =>
            cases assump_453
            case inl assump_455 =>
              cases assump_455
              case inl assump_457 =>
                apply False.elim assump_457
              case inr assump_458 =>
                have assump_943 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_468
                  apply False.elim assump_468
                let assump_467 := assump_452 assump_943
                apply False.elim assump_467
            case inr assump_456 =>
              cases assump_456
              case intro assump_474 assump_475 =>
                exact assump_475
      case inr assump_448 =>
        cases assump_1
        case intro assump_486 assump_487 =>
          cases assump_486
          case intro assump_488 assump_489 =>
            cases assump_488
            case inl assump_490 =>
              cases assump_490
              case inl assump_492 =>
                apply False.elim assump_492
              case inr assump_493 =>
                have assump_944 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_503
                  apply False.elim assump_503
                let assump_502 := assump_487 assump_944
                apply False.elim assump_502
            case inr assump_491 =>
              cases assump_491
              case intro assump_509 assump_510 =>
                exact assump_510
    case inr assump_446 =>
      cases assump_446
      case inl assump_519 =>
        cases assump_1
        case intro assump_523 assump_524 =>
          cases assump_523
          case intro assump_525 assump_526 =>
            cases assump_525
            case inl assump_527 =>
              cases assump_527
              case inl assump_529 =>
                apply False.elim assump_529
              case inr assump_530 =>
                have assump_945 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_540
                  apply False.elim assump_540
                let assump_539 := assump_524 assump_945
                apply False.elim assump_539
            case inr assump_528 =>
              cases assump_528
              case intro assump_546 assump_547 =>
                exact assump_547
      case inr assump_520 =>
        cases assump_1
        case intro assump_558 assump_559 =>
          cases assump_558
          case intro assump_560 assump_561 =>
            cases assump_560
            case inl assump_562 =>
              cases assump_562
              case inl assump_564 =>
                apply False.elim assump_564
              case inr assump_565 =>
                have assump_946 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_575
                  apply False.elim assump_575
                let assump_574 := assump_559 assump_946
                apply False.elim assump_574
            case inr assump_563 =>
              cases assump_563
              case intro assump_581 assump_582 =>
                exact assump_582
  case inr assump_444 =>
    cases assump_444
    case inl assump_591 =>
      cases assump_591
      case intro assump_593 assump_594 =>
        cases assump_1
        case intro assump_599 assump_600 =>
          cases assump_599
          case intro assump_601 assump_602 =>
            cases assump_601
            case inl assump_603 =>
              cases assump_603
              case inl assump_605 =>
                apply False.elim assump_605
              case inr assump_606 =>
                have assump_947 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_616
                  apply False.elim assump_616
                let assump_615 := assump_600 assump_947
                apply False.elim assump_615
            case inr assump_604 =>
              cases assump_604
              case intro assump_622 assump_623 =>
                exact assump_623
    case inr assump_592 =>
      cases assump_1
      case intro assump_634 assump_635 =>
        cases assump_634
        case intro assump_636 assump_637 =>
          cases assump_636
          case inl assump_638 =>
            cases assump_638
            case inl assump_640 =>
              apply False.elim assump_640
            case inr assump_641 =>
              have assump_948 : ((False → False) ∨ (p2 ∧ p1)) := by
                apply Or.inl
                intro assump_651
                apply False.elim assump_651
              let assump_650 := assump_635 assump_948
              apply False.elim assump_650
          case inr assump_639 =>
            cases assump_639
            case intro assump_657 assump_658 =>
              exact assump_658
  cases assump_2
  case inl assump_667 =>
    cases assump_667
    case inl assump_669 =>
      cases assump_669
      case inl assump_671 =>
        cases assump_1
        case intro assump_675 assump_676 =>
          cases assump_675
          case intro assump_677 assump_678 =>
            cases assump_677
            case inl assump_679 =>
              cases assump_679
              case inl assump_681 =>
                apply False.elim assump_681
              case inr assump_682 =>
                have assump_949 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_692
                  apply False.elim assump_692
                let assump_691 := assump_676 assump_949
                apply False.elim assump_691
            case inr assump_680 =>
              cases assump_680
              case intro assump_698 assump_699 =>
                have assump_950 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_709
                  apply False.elim assump_709
                let assump_708 := assump_676 assump_950
                apply False.elim assump_708
      case inr assump_672 =>
        cases assump_1
        case intro assump_717 assump_718 =>
          cases assump_717
          case intro assump_719 assump_720 =>
            cases assump_719
            case inl assump_721 =>
              cases assump_721
              case inl assump_723 =>
                apply False.elim assump_723
              case inr assump_724 =>
                have assump_951 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_734
                  apply False.elim assump_734
                let assump_733 := assump_718 assump_951
                apply False.elim assump_733
            case inr assump_722 =>
              cases assump_722
              case intro assump_740 assump_741 =>
                have assump_952 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_751
                  apply False.elim assump_751
                let assump_750 := assump_718 assump_952
                apply False.elim assump_750
    case inr assump_670 =>
      cases assump_670
      case inl assump_757 =>
        cases assump_1
        case intro assump_761 assump_762 =>
          cases assump_761
          case intro assump_763 assump_764 =>
            cases assump_763
            case inl assump_765 =>
              cases assump_765
              case inl assump_767 =>
                apply False.elim assump_767
              case inr assump_768 =>
                have assump_953 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_778
                  apply False.elim assump_778
                let assump_777 := assump_762 assump_953
                apply False.elim assump_777
            case inr assump_766 =>
              cases assump_766
              case intro assump_784 assump_785 =>
                have assump_954 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_795
                  apply False.elim assump_795
                let assump_794 := assump_762 assump_954
                apply False.elim assump_794
      case inr assump_758 =>
        cases assump_1
        case intro assump_803 assump_804 =>
          cases assump_803
          case intro assump_805 assump_806 =>
            cases assump_805
            case inl assump_807 =>
              cases assump_807
              case inl assump_809 =>
                apply False.elim assump_809
              case inr assump_810 =>
                have assump_955 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_820
                  apply False.elim assump_820
                let assump_819 := assump_804 assump_955
                apply False.elim assump_819
            case inr assump_808 =>
              cases assump_808
              case intro assump_826 assump_827 =>
                have assump_956 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_837
                  apply False.elim assump_837
                let assump_836 := assump_804 assump_956
                apply False.elim assump_836
  case inr assump_668 =>
    cases assump_668
    case inl assump_843 =>
      cases assump_843
      case intro assump_845 assump_846 =>
        cases assump_1
        case intro assump_851 assump_852 =>
          cases assump_851
          case intro assump_853 assump_854 =>
            cases assump_853
            case inl assump_855 =>
              cases assump_855
              case inl assump_857 =>
                apply False.elim assump_857
              case inr assump_858 =>
                have assump_957 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_868
                  apply False.elim assump_868
                let assump_867 := assump_852 assump_957
                apply False.elim assump_867
            case inr assump_856 =>
              cases assump_856
              case intro assump_874 assump_875 =>
                have assump_958 : ((False → False) ∨ (p2 ∧ p1)) := by
                  apply Or.inl
                  intro assump_885
                  apply False.elim assump_885
                let assump_884 := assump_852 assump_958
                apply False.elim assump_884
    case inr assump_844 =>
      cases assump_1
      case intro assump_893 assump_894 =>
        cases assump_893
        case intro assump_895 assump_896 =>
          cases assump_895
          case inl assump_897 =>
            cases assump_897
            case inl assump_899 =>
              apply False.elim assump_899
            case inr assump_900 =>
              have assump_959 : ((False → False) ∨ (p2 ∧ p1)) := by
                apply Or.inl
                intro assump_910
                apply False.elim assump_910
              let assump_909 := assump_894 assump_959
              apply False.elim assump_909
          case inr assump_898 =>
            cases assump_898
            case intro assump_916 assump_917 =>
              have assump_960 : ((False → False) ∨ (p2 ∧ p1)) := by
                apply Or.inl
                intro assump_927
                apply False.elim assump_927
              let assump_926 := assump_894 assump_960
              apply False.elim assump_926


variable (p3 p0 p7 p4 p2 p1 : Prop)
theorem file21_65843 : (((((p4 → False) → (False → p1)) ∧ ((p7 → True) → (p1 ∧ False))) ∨ (((p0 → True) → (False → p7)) → False)) → ((((p0 ∧ p2) ∨ (p4 → False)) ∧ ((p2 → False) ∨ (True ∧ p2))) → (((p3 ∨ p0) ∨ (p4 ∧ p1)) ∨ ((p7 → False) ∧ (False → p7))))) := by
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
          cases assump_1
          case inl assump_17 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              apply Or.inl
              apply Or.inl
              apply Or.inr
              exact assump_7
          case inr assump_18 =>
            apply Or.inl
            apply Or.inl
            apply Or.inr
            exact assump_7
        case inr assump_14 =>
          cases assump_14
          case intro assump_27 assump_28 =>
            cases assump_1
            case inl assump_33 =>
              cases assump_33
              case intro assump_35 assump_36 =>
                apply Or.inl
                apply Or.inl
                apply Or.inr
                exact assump_7
            case inr assump_34 =>
              apply Or.inl
              apply Or.inl
              apply Or.inr
              exact assump_7
    case inr assump_6 =>
      cases assump_4
      case inl assump_45 =>
        cases assump_1
        case inl assump_49 =>
          cases assump_49
          case intro assump_51 assump_52 =>
            apply Or.inr
            apply And.intro
            intro assump_57
            have assump_133 : (p7 → True) := by
              intro assump_62
              apply True.intro
            let assump_61 := assump_52 assump_133
            let assump_63 := And.right assump_61
            apply False.elim assump_63
            intro assump_68
            apply False.elim assump_68
        case inr assump_50 =>
          apply Or.inr
          apply And.intro
          intro assump_73
          have assump_134 : ((p0 → True) → (False → p7)) := by
            intro assump_78
            intro assump_79
            apply False.elim assump_79
          let assump_77 := assump_50 assump_134
          apply False.elim assump_77
          intro assump_85
          apply False.elim assump_85
      case inr assump_46 =>
        cases assump_46
        case intro assump_88 assump_89 =>
          cases assump_1
          case inl assump_94 =>
            cases assump_94
            case intro assump_96 assump_97 =>
              apply Or.inr
              apply And.intro
              intro assump_102
              have assump_135 : (p7 → True) := by
                intro assump_107
                apply True.intro
              let assump_106 := assump_97 assump_135
              let assump_108 := And.right assump_106
              apply False.elim assump_108
              intro assump_113
              apply False.elim assump_113
          case inr assump_95 =>
            apply Or.inr
            apply And.intro
            intro assump_118
            have assump_136 : ((p0 → True) → (False → p7)) := by
              intro assump_123
              intro assump_124
              apply False.elim assump_124
            let assump_122 := assump_95 assump_136
            apply False.elim assump_122
            intro assump_130
            apply False.elim assump_130


variable (p7 p4 p1 p6 p0 p3 p5 p2 : Prop)
theorem file21_69360 : (((((p7 ∧ p2) ∧ (p5 ∧ p0)) ∧ ((p0 ∧ False) → False)) → (((p4 → p5) → (p7 → False)) ∨ ((p5 → False) → (p3 ∧ p0)))) → ((((p6 ∨ p3) → False) → ((p6 → False) ∨ (p0 ∨ True))) ∨ (((p4 ∧ p7) ∨ (p0 ∧ p2)) → ((p1 ∨ True) ∨ (p0 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply Or.inl
  intro assump_7
  have assump_15 : (p6 ∨ p3) := by
    apply Or.inl
    exact assump_7
  let assump_11 := assump_4 assump_15
  apply False.elim assump_11


variable (p1 p7 p5 : Prop)
theorem file21_69867 : ((((((True ∨ p1) → False) → False) → False) ∨ ((((False → False) → False) → ((p7 ∧ p5) ∨ (p7 ∨ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_33 : (((True ∨ p1) → False) → False) := by
      intro assump_7
      have assump_34 : (True ∨ p1) := by
        apply Or.inl
        apply True.intro
      let assump_10 := assump_7 assump_34
      apply False.elim assump_10
    let assump_6 := assump_2 assump_33
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_35 : (((False → False) → False) → ((p7 ∧ p5) ∨ (p7 ∨ False))) := by
      intro assump_20
      have assump_36 : (False → False) := by
        intro assump_24
        apply False.elim assump_24
      let assump_23 := assump_20 assump_36
      apply False.elim assump_23
    let assump_19 := assump_3 assump_35
    apply False.elim assump_19


variable (p4 p6 p5 p7 : Prop)
theorem file21_70798 : (((((p6 → p6) → (False → False)) ∨ ((p5 → False) ∧ (p7 → p4))) → False) → False) := by
  intro assump_10
  have assump_21 : (((p6 → p6) → (False → False)) ∨ ((p5 → False) ∧ (p7 → p4))) := by
    apply Or.inl
    intro assump_14
    intro assump_15
    apply False.elim assump_15
  let assump_13 := assump_10 assump_21
  apply False.elim assump_13


variable (p5 p3 p0 p7 p4 p1 p2 : Prop)
theorem file21_71208 : (((((p1 → p2) ∨ (p7 ∨ p7)) ∨ ((p1 ∧ p5) → False)) ∧ (((False → p0) ∨ (p1 ∨ p5)) → False)) → ((((p5 ∨ p4) ∨ (p4 ∨ p5)) ∨ ((True ∨ p5) ∨ (True → p3))) → (((p2 ∧ p2) ∧ (p5 ∨ False)) → ((p4 → False) → (p0 ∨ p5))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_8
      case inl assump_15 =>
        cases assump_2
        case inl assump_19 =>
          cases assump_19
          case inl assump_21 =>
            cases assump_21
            case inl assump_23 =>
              cases assump_1
              case intro assump_27 assump_28 =>
                cases assump_27
                case inl assump_29 =>
                  cases assump_29
                  case inl assump_31 =>
                    apply Or.inr
                    exact assump_23
                  case inr assump_32 =>
                    cases assump_32
                    case inl assump_37 =>
                      apply Or.inr
                      exact assump_23
                    case inr assump_38 =>
                      apply Or.inr
                      exact assump_23
                case inr assump_30 =>
                  apply Or.inr
                  exact assump_23
            case inr assump_24 =>
              cases assump_1
              case intro assump_53 assump_54 =>
                cases assump_53
                case inl assump_55 =>
                  cases assump_55
                  case inl assump_57 =>
                    apply Or.inr
                    exact assump_15
                  case inr assump_58 =>
                    cases assump_58
                    case inl assump_63 =>
                      apply Or.inr
                      exact assump_15
                    case inr assump_64 =>
                      apply Or.inr
                      exact assump_15
                case inr assump_56 =>
                  apply Or.inr
                  exact assump_15
          case inr assump_22 =>
            cases assump_22
            case inl assump_77 =>
              cases assump_1
              case intro assump_81 assump_82 =>
                cases assump_81
                case inl assump_83 =>
                  cases assump_83
                  case inl assump_85 =>
                    apply Or.inr
                    exact assump_15
                  case inr assump_86 =>
                    cases assump_86
                    case inl assump_91 =>
                      apply Or.inr
                      exact assump_15
                    case inr assump_92 =>
                      apply Or.inr
                      exact assump_15
                case inr assump_84 =>
                  apply Or.inr
                  exact assump_15
            case inr assump_78 =>
              cases assump_1
              case intro assump_107 assump_108 =>
                cases assump_107
                case inl assump_109 =>
                  cases assump_109
                  case inl assump_111 =>
                    apply Or.inr
                    exact assump_78
                  case inr assump_112 =>
                    cases assump_112
                    case inl assump_117 =>
                      apply Or.inr
                      exact assump_78
                    case inr assump_118 =>
                      apply Or.inr
                      exact assump_78
                case inr assump_110 =>
                  apply Or.inr
                  exact assump_78
        case inr assump_20 =>
          cases assump_20
          case inl assump_131 =>
            cases assump_131
            case inl assump_133 =>
              cases assump_1
              case intro assump_137 assump_138 =>
                cases assump_137
                case inl assump_139 =>
                  cases assump_139
                  case inl assump_141 =>
                    apply Or.inr
                    exact assump_15
                  case inr assump_142 =>
                    cases assump_142
                    case inl assump_147 =>
                      apply Or.inr
                      exact assump_15
                    case inr assump_148 =>
                      apply Or.inr
                      exact assump_15
                case inr assump_140 =>
                  apply Or.inr
                  exact assump_15
            case inr assump_134 =>
              cases assump_1
              case intro assump_163 assump_164 =>
                cases assump_163
                case inl assump_165 =>
                  cases assump_165
                  case inl assump_167 =>
                    apply Or.inr
                    exact assump_134
                  case inr assump_168 =>
                    cases assump_168
                    case inl assump_173 =>
                      apply Or.inr
                      exact assump_134
                    case inr assump_174 =>
                      apply Or.inr
                      exact assump_134
                case inr assump_166 =>
                  apply Or.inr
                  exact assump_134
          case inr assump_132 =>
            cases assump_1
            case intro assump_189 assump_190 =>
              cases assump_189
              case inl assump_191 =>
                cases assump_191
                case inl assump_193 =>
                  apply Or.inr
                  exact assump_15
                case inr assump_194 =>
                  cases assump_194
                  case inl assump_199 =>
                    apply Or.inr
                    exact assump_15
                  case inr assump_200 =>
                    apply Or.inr
                    exact assump_15
              case inr assump_192 =>
                apply Or.inr
                exact assump_15
      case inr assump_16 =>
        apply False.elim assump_16


variable (p6 p2 p1 p7 p0 p3 p4 : Prop)
theorem file21_77234 : ((((((False ∧ False) → False) → ((p0 ∨ p3) → False)) → (((p7 ∧ p6) ∧ (True → False)) → ((False ∧ p2) ∨ (p4 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((False ∧ False) → False) → ((p0 ∨ p3) → False)) → (((p7 ∧ p6) ∧ (True → False)) → ((False ∧ p2) ∨ (p4 ∨ p1)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        have assump_34 : True := by
          apply True.intro
        let assump_26 := assump_8 assump_34
        apply False.elim assump_26
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p6 p1 p5 p3 p4 p2 p7 p0 : Prop)
theorem file21_77956 : (((((False ∧ p4) ∧ (p1 → False)) ∧ ((p6 ∧ p6) → (p7 → False))) → (((p2 ∨ p3) ∨ (p2 ∧ p5)) → False)) ∨ ((((p2 ∧ p0) → (p0 → p3)) → False) → (((p0 ∨ p3) → (False ∧ False)) ∧ ((p3 → False) ∧ (p6 ∨ p6))))) := by
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
          case intro assump_13 assump_14 =>
            apply False.elim assump_13
    case inr assump_6 =>
      cases assump_1
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            apply False.elim assump_23
  case inr assump_4 =>
    cases assump_4
    case intro assump_27 assump_28 =>
      cases assump_1
      case intro assump_33 assump_34 =>
        cases assump_33
        case intro assump_35 assump_36 =>
          cases assump_35
          case intro assump_37 assump_38 =>
            apply False.elim assump_37


variable (p2 p4 p5 p6 p1 p0 : Prop)
theorem file21_79168 : ((((((p5 ∧ p1) ∧ (p0 ∨ p2)) ∨ ((p6 → False) ∧ (False → True))) → (((p6 ∨ False) ∨ (p1 ∨ p4)) → False)) ∧ ((((p5 ∧ p1) ∧ (True ∨ True)) ∧ ((p6 → p4) ∨ (p6 ∧ p5))) ∧ (((p1 ∨ p4) ∧ (True → False)) ∧ ((False → False) ∨ (False → False))))) → False) := by
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
              cases assump_9
              case inl assump_22 =>
                cases assump_7
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case inl assump_30 =>
                      cases assump_27
                      case inl assump_36 =>
                        have assump_228 : True := by
                          apply True.intro
                        let assump_41 := assump_29 assump_228
                        apply False.elim assump_41
                      case inr assump_37 =>
                        have assump_229 : True := by
                          apply True.intro
                        let assump_48 := assump_29 assump_229
                        apply False.elim assump_48
                    case inr assump_31 =>
                      cases assump_27
                      case inl assump_56 =>
                        have assump_230 : True := by
                          apply True.intro
                        let assump_61 := assump_29 assump_230
                        apply False.elim assump_61
                      case inr assump_57 =>
                        have assump_231 : True := by
                          apply True.intro
                        let assump_68 := assump_29 assump_231
                        apply False.elim assump_68
              case inr assump_23 =>
                cases assump_23
                case intro assump_72 assump_73 =>
                  cases assump_7
                  case intro assump_78 assump_79 =>
                    cases assump_78
                    case intro assump_80 assump_81 =>
                      cases assump_80
                      case inl assump_82 =>
                        cases assump_79
                        case inl assump_88 =>
                          have assump_232 : True := by
                            apply True.intro
                          let assump_93 := assump_81 assump_232
                          apply False.elim assump_93
                        case inr assump_89 =>
                          have assump_233 : True := by
                            apply True.intro
                          let assump_100 := assump_81 assump_233
                          apply False.elim assump_100
                      case inr assump_83 =>
                        cases assump_79
                        case inl assump_108 =>
                          have assump_234 : True := by
                            apply True.intro
                          let assump_113 := assump_81 assump_234
                          apply False.elim assump_113
                        case inr assump_109 =>
                          have assump_235 : True := by
                            apply True.intro
                          let assump_120 := assump_81 assump_235
                          apply False.elim assump_120
            case inr assump_19 =>
              cases assump_9
              case inl assump_126 =>
                cases assump_7
                case intro assump_130 assump_131 =>
                  cases assump_130
                  case intro assump_132 assump_133 =>
                    cases assump_132
                    case inl assump_134 =>
                      cases assump_131
                      case inl assump_140 =>
                        have assump_236 : True := by
                          apply True.intro
                        let assump_145 := assump_133 assump_236
                        apply False.elim assump_145
                      case inr assump_141 =>
                        have assump_237 : True := by
                          apply True.intro
                        let assump_152 := assump_133 assump_237
                        apply False.elim assump_152
                    case inr assump_135 =>
                      cases assump_131
                      case inl assump_160 =>
                        have assump_238 : True := by
                          apply True.intro
                        let assump_165 := assump_133 assump_238
                        apply False.elim assump_165
                      case inr assump_161 =>
                        have assump_239 : True := by
                          apply True.intro
                        let assump_172 := assump_133 assump_239
                        apply False.elim assump_172
              case inr assump_127 =>
                cases assump_127
                case intro assump_176 assump_177 =>
                  cases assump_7
                  case intro assump_182 assump_183 =>
                    cases assump_182
                    case intro assump_184 assump_185 =>
                      cases assump_184
                      case inl assump_186 =>
                        cases assump_183
                        case inl assump_192 =>
                          have assump_240 : True := by
                            apply True.intro
                          let assump_197 := assump_185 assump_240
                          apply False.elim assump_197
                        case inr assump_193 =>
                          have assump_241 : True := by
                            apply True.intro
                          let assump_204 := assump_185 assump_241
                          apply False.elim assump_204
                      case inr assump_187 =>
                        cases assump_183
                        case inl assump_212 =>
                          have assump_242 : True := by
                            apply True.intro
                          let assump_217 := assump_185 assump_242
                          apply False.elim assump_217
                        case inr assump_213 =>
                          have assump_243 : True := by
                            apply True.intro
                          let assump_224 := assump_185 assump_243
                          apply False.elim assump_224


variable (p0 : Prop)
theorem file21_85923 : (((((p0 → True) → False) → False) → False) → False) := by
  intro assump_1
  have assump_16 : (((p0 → True) → False) → False) := by
    intro assump_5
    have assump_17 : (p0 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p7 p2 : Prop)
theorem file21_86339 : ((((((True ∨ False) ∨ (False → p2)) → ((p7 ∧ False) ∧ (p7 → True))) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((True ∨ False) ∨ (False → p2)) → ((p7 ∧ False) ∧ (p7 → True))) → False) := by
    intro assump_5
    have assump_19 : ((True ∨ False) ∨ (False → p2)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_19
    let assump_9 := And.left assump_8
    let assump_10 := And.right assump_9
    apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p5 p0 p7 p4 p6 p2 : Prop)
theorem file21_86972 : (((((p4 → False) → (False ∨ p7)) → False) → (((p5 ∧ False) ∨ (p1 → p1)) ∨ ((p1 ∨ True) → False))) ∨ ((((p6 → False) ∧ (p7 ∧ p5)) ∧ ((p2 → False) ∨ (False ∨ p2))) → (((True → False) → (p0 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  exact assump_4


variable (p1 p3 p5 p2 p6 p7 p4 p0 : Prop)
theorem file21_87348 : (((((p4 → False) ∨ (p3 ∨ p2)) → False) ∧ (((p4 → p5) ∧ (p4 ∧ p2)) → ((False ∧ p1) ∨ (p0 ∨ p7)))) → ((((True → False) → (p7 ∨ p2)) ∨ ((p0 → False) → (p7 → False))) ∨ (((p3 ∨ True) ∨ (p4 ∨ p0)) → ((p6 ∧ p1) ∧ (p6 ∧ p5))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_8
    have assump_15 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_15
    apply False.elim assump_11


variable (p0 p6 p1 p7 p5 p3 p2 : Prop)
theorem file21_87885 : (((((p0 ∨ False) → False) ∨ ((p6 → p1) ∨ (False → p6))) ∧ (((p1 ∧ False) → (p2 → False)) → False)) → ((((p3 ∧ p7) ∨ (p5 → p7)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      have assump_65 : ((p1 ∧ False) → (p2 → False)) := by
        intro assump_14
        intro assump_15
        cases assump_14
        case intro assump_18 assump_19 =>
          apply False.elim assump_19
      let assump_13 := assump_6 assump_65
      apply False.elim assump_13
    case inr assump_8 =>
      cases assump_8
      case inl assump_27 =>
        have assump_66 : ((p1 ∧ False) → (p2 → False)) := by
          intro assump_34
          intro assump_35
          cases assump_34
          case intro assump_38 assump_39 =>
            apply False.elim assump_39
        let assump_33 := assump_6 assump_66
        apply False.elim assump_33
      case inr assump_28 =>
        have assump_67 : ((p1 ∧ False) → (p2 → False)) := by
          intro assump_52
          intro assump_53
          cases assump_52
          case intro assump_56 assump_57 =>
            apply False.elim assump_57
        let assump_51 := assump_6 assump_67
        apply False.elim assump_51


variable (p7 p0 p4 p3 p1 p6 p5 : Prop)
theorem file21_89218 : (((((True → False) ∨ (p1 ∨ False)) ∧ ((p7 → False) → False)) → (((p7 → p3) ∧ (p5 → p7)) → ((p4 → False) ∨ (p0 ∧ p5)))) → ((((p6 → False) ∨ (p3 ∨ p0)) → ((p0 → p0) ∨ (True → False))) ∨ (((p3 → p7) → (p7 ∨ p7)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    apply Or.inl
    intro assump_9
    exact assump_9
  case inr assump_6 =>
    cases assump_6
    case inl assump_12 =>
      apply Or.inl
      intro assump_16
      exact assump_16
    case inr assump_13 =>
      apply Or.inl
      intro assump_21
      exact assump_21


variable (p4 p7 p3 p2 p0 p5 : Prop)
theorem file21_89868 : (((((p3 ∨ p2) ∧ (p0 ∧ p4)) ∨ ((p5 ∨ p7) ∨ (p5 → False))) → False) → False) := by
  intro assump_1
  have assump_16 : (((p3 ∨ p2) ∧ (p0 ∧ p4)) ∨ ((p5 ∨ p7) ∨ (p5 → False))) := by
    apply Or.inr
    apply Or.inr
    intro assump_5
    have assump_17 : (((p3 ∨ p2) ∧ (p0 ∧ p4)) ∨ ((p5 ∨ p7) ∨ (p5 → False))) := by
      apply Or.inr
      apply Or.inl
      apply Or.inl
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 p0 p5 p2 p3 p7 p1 p4 : Prop)
theorem file21_90459 : (((((p1 → p1) ∧ (p1 → True)) → False) → (((p1 ∨ p2) → (p4 → False)) → ((p3 → p0) → (p4 → False)))) ∨ ((((p6 → p5) ∨ (True ∧ p1)) → ((p3 ∨ p4) ∨ (p5 ∧ p4))) ∧ (((p0 ∧ p6) → False) ∧ ((True ∧ p2) ∨ (p7 ∧ True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  have assump_21 : ((p1 → p1) ∧ (p1 → True)) := by
    apply And.intro
    intro assump_14
    exact assump_14
    intro assump_17
    apply True.intro
  let assump_13 := assump_1 assump_21
  apply False.elim assump_13


variable (p3 p6 p1 p4 p0 p2 p5 : Prop)
theorem file21_91042 : (((((p3 ∨ True) ∨ (p1 ∧ p6)) → False) → False) ∨ ((((p3 → p6) → False) ∧ ((p4 → False) → (p3 ∧ p0))) ∧ (((p2 → False) ∨ (True ∧ p4)) ∧ ((p5 ∧ False) ∨ (p2 → p0))))) := by
  apply Or.inl
  intro assump_27
  have assump_34 : ((p3 ∨ True) ∨ (p1 ∧ p6)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_30 := assump_27 assump_34
  apply False.elim assump_30


variable (p0 p2 p1 p3 p6 p5 : Prop)
theorem file21_91480 : (((((False → p0) ∨ (True ∨ p5)) → ((p3 ∧ False) → False)) → (((True ∨ p1) ∨ (True ∧ p0)) → False)) → ((((p5 ∧ p3) ∧ (p2 ∧ p0)) → False) → (((p0 → p6) → (False ∧ False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_23 : (((False → p0) ∨ (True ∨ p5)) → ((p3 ∧ False) → False)) := by
    intro assump_11
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      apply False.elim assump_14
  let assump_10 := assump_1 assump_23
  have assump_24 : ((True ∨ p1) ∨ (True ∧ p0)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_19 := assump_10 assump_24
  apply False.elim assump_19


variable (p3 p6 p7 : Prop)
theorem file21_92194 : ((((((False → p6) ∧ (False ∧ p7)) ∧ ((True → False) ∧ (p7 ∨ p3))) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((False → p6) ∧ (False ∧ p7)) ∧ ((True → False) ∧ (p7 ∨ p3))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p7 p0 p2 p6 p3 p5 p1 : Prop)
theorem file21_92771 : (((((p3 ∨ p7) ∧ (False ∧ False)) ∧ ((p2 → False) → False)) → (((p1 → p2) → False) ∨ ((p1 → p6) ∨ (p1 ∨ p7)))) ∨ ((((p2 ∧ p0) ∨ (p0 ∧ True)) ∨ ((p6 → False) → (p5 → p2))) ∨ (((True → p3) → (True ∨ p2)) → False))) := by
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
          apply False.elim assump_10
      case inr assump_7 =>
        cases assump_5
        case intro assump_16 assump_17 =>
          apply False.elim assump_16


variable (p6 p7 p0 p5 p4 p1 p3 : Prop)
theorem file21_93469 : (((((p0 → False) → (p3 → True)) ∨ ((p1 → p4) ∧ (p3 → p1))) → False) → ((((p4 ∧ p7) ∧ (False ∨ p6)) ∧ ((p3 ∨ False) → False)) ∧ (((p4 ∨ p7) ∨ (p3 ∨ p5)) ∨ ((p3 ∧ p7) → False)))) := by
  intro assump_13
  apply And.intro
  apply And.intro
  apply And.intro
  apply And.intro
  have assump_70 : (((p0 → False) → (p3 → True)) ∨ ((p1 → p4) ∧ (p3 → p1))) := by
    apply Or.inl
    intro assump_17
    intro assump_18
    apply True.intro
  let assump_16 := assump_13 assump_70
  apply False.elim assump_16
  have assump_71 : (((p0 → False) → (p3 → True)) ∨ ((p1 → p4) ∧ (p3 → p1))) := by
    apply Or.inl
    intro assump_25
    intro assump_26
    apply True.intro
  let assump_24 := assump_13 assump_71
  apply False.elim assump_24
  have assump_72 : (((p0 → False) → (p3 → True)) ∨ ((p1 → p4) ∧ (p3 → p1))) := by
    apply Or.inl
    intro assump_33
    intro assump_34
    apply True.intro
  let assump_32 := assump_13 assump_72
  apply False.elim assump_32
  intro assump_38
  cases assump_38
  case inl assump_39 =>
    have assump_73 : (((p0 → False) → (p3 → True)) ∨ ((p1 → p4) ∧ (p3 → p1))) := by
      apply Or.inl
      intro assump_46
      intro assump_47
      apply True.intro
    let assump_45 := assump_13 assump_73
    apply False.elim assump_45
  case inr assump_40 =>
    apply False.elim assump_40
  apply Or.inr
  intro assump_55
  cases assump_55
  case intro assump_56 assump_57 =>
    have assump_74 : (((p0 → False) → (p3 → True)) ∨ ((p1 → p4) ∧ (p3 → p1))) := by
      apply Or.inl
      intro assump_65
      intro assump_66
      apply True.intro
    let assump_64 := assump_13 assump_74
    apply False.elim assump_64


variable (p7 p3 p2 p1 p6 : Prop)
theorem file21_95169 : ((((((p1 → p7) → False) ∧ ((p6 ∨ p7) → False)) → False) ∧ ((((True ∨ p3) → False) → ((p2 → False) → (p6 ∨ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((True ∨ p3) → False) → ((p2 → False) → (p6 ∨ p1))) := by
      intro assump_9
      intro assump_10
      have assump_23 : (True ∨ p3) := by
        apply Or.inl
        apply True.intro
      let assump_15 := assump_9 assump_23
      apply False.elim assump_15
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p5 p6 p3 p4 p1 : Prop)
theorem file21_95785 : (((((True ∨ p5) ∨ (p4 → p3)) → False) → (((p3 → False) → (p4 → p1)) → False)) ∨ ((((False → False) → (p4 ∧ p1)) ∧ ((True → False) ∧ (p6 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_11 : ((True ∨ p5) ∨ (p4 → p3)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p4 p6 p1 : Prop)
theorem file21_96219 : (((((True ∨ p4) → (False → False)) ∨ ((p1 ∧ p6) → False)) → False) → False) := by
  intro assump_1
  have assump_12 : (((True ∨ p4) → (False → False)) ∨ ((p1 ∧ p6) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p6 p7 p5 p3 p1 p2 : Prop)
theorem file21_96609 : ((((((False ∧ p6) → (True → False)) ∧ ((p7 → p3) → (p6 → p6))) ∨ (((p6 ∨ p5) → (True ∨ p1)) ∨ ((p2 → False) ∨ (p6 ∨ p5)))) → ((((False ∧ p6) ∧ (p1 → False)) → ((p7 ∨ p1) → False)) → False)) → False) := by
  intro assump_1
  have assump_43 : ((((False ∧ p6) → (True → False)) ∧ ((p7 → p3) → (p6 → p6))) ∨ (((p6 ∨ p5) → (True ∨ p1)) ∨ ((p2 → False) ∨ (p6 ∨ p5)))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
    intro assump_13
    intro assump_14
    exact assump_14
  let assump_4 := assump_1 assump_43
  have assump_44 : (((False ∧ p6) ∧ (p1 → False)) → ((p7 ∨ p1) → False)) := by
    intro assump_20
    intro assump_21
    cases assump_21
    case inl assump_22 =>
      cases assump_20
      case intro assump_26 assump_27 =>
        cases assump_26
        case intro assump_28 assump_29 =>
          apply False.elim assump_28
    case inr assump_23 =>
      cases assump_20
      case intro assump_34 assump_35 =>
        cases assump_34
        case intro assump_36 assump_37 =>
          apply False.elim assump_36
  let assump_19 := assump_4 assump_44
  apply False.elim assump_19


variable (p1 p6 p5 p7 p3 : Prop)
theorem file21_97882 : (((((p3 → False) ∨ (False ∧ p1)) → ((p6 → p7) ∨ (p3 ∨ p6))) ∧ (((p1 → False) ∧ (p5 ∨ p1)) ∧ ((p5 ∧ True) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_32 : (p5 ∧ True) := by
            apply And.intro
            exact assump_12
            apply True.intro
          let assump_18 := assump_7 assump_32
          apply False.elim assump_18
        case inr assump_13 =>
          have assump_33 : p1 := by
            exact assump_13
          let assump_28 := assump_8 assump_33
          apply False.elim assump_28


variable (p6 p1 p3 : Prop)
theorem file21_98689 : (((((False ∨ p1) ∨ (p6 → p3)) → ((True → False) → False)) → False) → False) := by
  intro assump_1
  have assump_32 : (((False ∨ p1) ∨ (p6 → p3)) → ((True → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        apply False.elim assump_11
      case inr assump_12 =>
        have assump_33 : True := by
          apply True.intro
        let assump_18 := assump_6 assump_33
        apply False.elim assump_18
    case inr assump_10 =>
      have assump_34 : True := by
        apply True.intro
      let assump_25 := assump_6 assump_34
      apply False.elim assump_25
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p1 p3 p6 p0 p7 p5 : Prop)
theorem file21_99490 : (((((p7 → False) ∧ (p1 → False)) → False) ∧ (((p1 → False) ∧ (p3 → False)) ∨ ((p0 ∨ p6) → (p6 ∨ p7)))) → ((((p5 ∧ True) ∧ (p1 → True)) ∧ ((p3 ∧ False) → (p1 ∨ p5))) → (((p3 ∧ p3) ∨ (p3 ∨ p5)) ∧ ((False → False) ∨ (False → True))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_1
        case intro assump_17 assump_18 =>
          cases assump_18
          case inl assump_21 =>
            cases assump_21
            case intro assump_23 assump_24 =>
              apply Or.inr
              apply Or.inr
              exact assump_7
          case inr assump_22 =>
            apply Or.inr
            apply Or.inr
            exact assump_7
  cases assump_2
  case intro assump_31 assump_32 =>
    cases assump_31
    case intro assump_33 assump_34 =>
      cases assump_33
      case intro assump_35 assump_36 =>
        cases assump_1
        case intro assump_45 assump_46 =>
          cases assump_46
          case inl assump_49 =>
            cases assump_49
            case intro assump_51 assump_52 =>
              apply Or.inl
              intro assump_57
              apply False.elim assump_57
          case inr assump_50 =>
            apply Or.inl
            intro assump_62
            apply False.elim assump_62


variable (p6 p7 p3 p5 p4 p2 p0 : Prop)
theorem file21_100989 : ((((((p5 → True) → False) ∨ ((p3 ∧ p6) → (p4 ∨ p0))) ∧ (((p5 ∨ False) ∧ (False ∨ True)) ∨ ((p3 ∧ p5) ∧ (True ∨ False)))) ∧ ((((p7 ∧ False) → False) → ((False → p6) ∨ (True ∧ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_12
            case inl assump_14 =>
              cases assump_13
              case inl assump_18 =>
                apply False.elim assump_18
              case inr assump_19 =>
                have assump_120 : (((p7 ∧ False) → False) → ((False → p6) ∨ (True ∧ p2))) := by
                  intro assump_27
                  apply Or.inl
                  intro assump_30
                  apply False.elim assump_30
                let assump_26 := assump_3 assump_120
                apply False.elim assump_26
            case inr assump_15 =>
              apply False.elim assump_15
        case inr assump_11 =>
          cases assump_11
          case intro assump_38 assump_39 =>
            cases assump_38
            case intro assump_40 assump_41 =>
              cases assump_39
              case inl assump_46 =>
                have assump_121 : (((p7 ∧ False) → False) → ((False → p6) ∨ (True ∧ p2))) := by
                  intro assump_53
                  apply Or.inl
                  intro assump_56
                  apply False.elim assump_56
                let assump_52 := assump_3 assump_121
                apply False.elim assump_52
              case inr assump_47 =>
                apply False.elim assump_47
      case inr assump_7 =>
        cases assump_5
        case inl assump_66 =>
          cases assump_66
          case intro assump_68 assump_69 =>
            cases assump_68
            case inl assump_70 =>
              cases assump_69
              case inl assump_74 =>
                apply False.elim assump_74
              case inr assump_75 =>
                have assump_122 : (((p7 ∧ False) → False) → ((False → p6) ∨ (True ∧ p2))) := by
                  intro assump_83
                  apply Or.inl
                  intro assump_86
                  apply False.elim assump_86
                let assump_82 := assump_3 assump_122
                apply False.elim assump_82
            case inr assump_71 =>
              apply False.elim assump_71
        case inr assump_67 =>
          cases assump_67
          case intro assump_94 assump_95 =>
            cases assump_94
            case intro assump_96 assump_97 =>
              cases assump_95
              case inl assump_102 =>
                have assump_123 : (((p7 ∧ False) → False) → ((False → p6) ∨ (True ∧ p2))) := by
                  intro assump_109
                  apply Or.inl
                  intro assump_112
                  apply False.elim assump_112
                let assump_108 := assump_3 assump_123
                apply False.elim assump_108
              case inr assump_103 =>
                apply False.elim assump_103


variable (p3 p7 p6 p1 p5 p2 p4 p0 : Prop)
theorem file21_104258 : (((((True → False) → (p0 → p7)) ∨ ((p6 → p3) → (p4 → p7))) → False) → ((((False → p3) → (True → p2)) → False) → (((p1 ∨ True) ∨ (p5 ∧ p3)) → ((p2 ∨ True) → (p3 ∧ p6))))) := by
  intro assump_5
  intro assump_6
  intro assump_7
  intro assump_8
  apply And.intro
  cases assump_8
  case inl assump_9 =>
    cases assump_7
    case inl assump_13 =>
      cases assump_13
      case inl assump_15 =>
        have assump_265 : (((True → False) → (p0 → p7)) ∨ ((p6 → p3) → (p4 → p7))) := by
          apply Or.inl
          intro assump_24
          intro assump_25
          have assump_266 : True := by
            apply True.intro
          let assump_30 := assump_24 assump_266
          apply False.elim assump_30
        let assump_23 := assump_5 assump_265
        apply False.elim assump_23
      case inr assump_16 =>
        have assump_267 : (((True → False) → (p0 → p7)) ∨ ((p6 → p3) → (p4 → p7))) := by
          apply Or.inl
          intro assump_44
          intro assump_45
          have assump_268 : True := by
            apply True.intro
          let assump_50 := assump_44 assump_268
          apply False.elim assump_50
        let assump_43 := assump_5 assump_267
        apply False.elim assump_43
    case inr assump_14 =>
      cases assump_14
      case intro assump_57 assump_58 =>
        exact assump_58
  case inr assump_10 =>
    cases assump_7
    case inl assump_69 =>
      cases assump_69
      case inl assump_71 =>
        have assump_269 : (((True → False) → (p0 → p7)) ∨ ((p6 → p3) → (p4 → p7))) := by
          apply Or.inl
          intro assump_80
          intro assump_81
          have assump_270 : True := by
            apply True.intro
          let assump_86 := assump_80 assump_270
          apply False.elim assump_86
        let assump_79 := assump_5 assump_269
        apply False.elim assump_79
      case inr assump_72 =>
        have assump_271 : (((True → False) → (p0 → p7)) ∨ ((p6 → p3) → (p4 → p7))) := by
          apply Or.inl
          intro assump_100
          intro assump_101
          have assump_272 : True := by
            apply True.intro
          let assump_106 := assump_100 assump_272
          apply False.elim assump_106
        let assump_99 := assump_5 assump_271
        apply False.elim assump_99
    case inr assump_70 =>
      cases assump_70
      case intro assump_113 assump_114 =>
        exact assump_114
  cases assump_8
  case inl assump_123 =>
    cases assump_7
    case inl assump_127 =>
      cases assump_127
      case inl assump_129 =>
        have assump_273 : (((True → False) → (p0 → p7)) ∨ ((p6 → p3) → (p4 → p7))) := by
          apply Or.inl
          intro assump_138
          intro assump_139
          have assump_274 : True := by
            apply True.intro
          let assump_144 := assump_138 assump_274
          apply False.elim assump_144
        let assump_137 := assump_5 assump_273
        apply False.elim assump_137
      case inr assump_130 =>
        have assump_275 : (((True → False) → (p0 → p7)) ∨ ((p6 → p3) → (p4 → p7))) := by
          apply Or.inl
          intro assump_158
          intro assump_159
          have assump_276 : True := by
            apply True.intro
          let assump_164 := assump_158 assump_276
          apply False.elim assump_164
        let assump_157 := assump_5 assump_275
        apply False.elim assump_157
    case inr assump_128 =>
      cases assump_128
      case intro assump_171 assump_172 =>
        have assump_277 : (((True → False) → (p0 → p7)) ∨ ((p6 → p3) → (p4 → p7))) := by
          apply Or.inl
          intro assump_182
          intro assump_183
          have assump_278 : True := by
            apply True.intro
          let assump_188 := assump_182 assump_278
          apply False.elim assump_188
        let assump_181 := assump_5 assump_277
        apply False.elim assump_181
  case inr assump_124 =>
    cases assump_7
    case inl assump_197 =>
      cases assump_197
      case inl assump_199 =>
        have assump_279 : (((True → False) → (p0 → p7)) ∨ ((p6 → p3) → (p4 → p7))) := by
          apply Or.inl
          intro assump_208
          intro assump_209
          have assump_280 : True := by
            apply True.intro
          let assump_214 := assump_208 assump_280
          apply False.elim assump_214
        let assump_207 := assump_5 assump_279
        apply False.elim assump_207
      case inr assump_200 =>
        have assump_281 : (((True → False) → (p0 → p7)) ∨ ((p6 → p3) → (p4 → p7))) := by
          apply Or.inl
          intro assump_228
          intro assump_229
          have assump_282 : True := by
            apply True.intro
          let assump_234 := assump_228 assump_282
          apply False.elim assump_234
        let assump_227 := assump_5 assump_281
        apply False.elim assump_227
    case inr assump_198 =>
      cases assump_198
      case intro assump_241 assump_242 =>
        have assump_283 : (((True → False) → (p0 → p7)) ∨ ((p6 → p3) → (p4 → p7))) := by
          apply Or.inl
          intro assump_252
          intro assump_253
          have assump_284 : True := by
            apply True.intro
          let assump_258 := assump_252 assump_284
          apply False.elim assump_258
        let assump_251 := assump_5 assump_283
        apply False.elim assump_251


variable (p3 p2 p4 p1 p0 p7 p5 p6 : Prop)
theorem file21_109645 : (((((p2 → False) ∧ (p7 → False)) ∧ ((p6 ∧ p1) ∨ (True ∨ p5))) → (((p0 ∧ p7) → False) ∨ ((p4 → p5) → (p6 ∧ p2)))) → ((((True ∨ p6) ∨ (p7 ∨ p3)) ∧ ((p0 ∨ True) → False)) → (((True → False) → (True ∧ p6)) ∨ ((p3 ∧ p3) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        apply Or.inl
        intro assump_15
        apply And.intro
        apply True.intro
        have assump_59 : True := by
          apply True.intro
        let assump_18 := assump_15 assump_59
        apply False.elim assump_18
      case inr assump_8 =>
        apply Or.inl
        intro assump_28
        apply And.intro
        apply True.intro
        exact assump_8
    case inr assump_6 =>
      cases assump_6
      case inl assump_31 =>
        apply Or.inl
        intro assump_39
        apply And.intro
        apply True.intro
        have assump_60 : True := by
          apply True.intro
        let assump_42 := assump_39 assump_60
        apply False.elim assump_42
      case inr assump_32 =>
        apply Or.inl
        intro assump_52
        apply And.intro
        apply True.intro
        have assump_61 : True := by
          apply True.intro
        let assump_55 := assump_52 assump_61
        apply False.elim assump_55


variable (p7 p2 p4 p0 p6 p5 p1 : Prop)
theorem file21_111075 : (((((True ∧ p4) ∨ (p4 → True)) → ((p1 ∧ False) → (p5 ∧ True))) → False) → ((((p7 ∧ p0) ∧ (p2 → False)) ∧ ((p7 ∨ p0) → (p6 ∨ p7))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        have assump_31 : (((True ∧ p4) ∨ (p4 → True)) → ((p1 ∧ False) → (p5 ∧ True))) := by
          intro assump_20
          intro assump_21
          apply And.intro
          cases assump_21
          case intro assump_22 assump_23 =>
            apply False.elim assump_23
          apply True.intro
        let assump_19 := assump_1 assump_31
        apply False.elim assump_19


variable (p2 p3 p7 p4 p0 p1 p5 : Prop)
theorem file21_111868 : (((((False → False) → False) ∧ ((p5 ∧ p0) ∨ (p4 → False))) → (((p4 → False) ∧ (p3 → False)) → ((p5 ∧ p5) ∨ (p2 → p5)))) ∨ ((((p2 ∧ p7) → False) ∨ ((p1 ∨ p4) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      cases assump_10
      case inl assump_13 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply Or.inl
          apply And.intro
          exact assump_15
          exact assump_15
      case inr assump_14 =>
        apply Or.inr
        intro assump_23
        have assump_35 : (False → False) := by
          intro assump_29
          apply False.elim assump_29
        let assump_28 := assump_9 assump_35
        apply False.elim assump_28


variable (p2 p4 p6 p3 : Prop)
theorem file21_112740 : ((((((p3 → False) → (True ∨ p2)) ∨ ((False → False) ∨ (False → p3))) ∨ (((p6 → p2) ∨ (p4 ∨ p4)) ∨ ((p2 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p3 → False) → (True ∨ p2)) ∨ ((False → False) ∨ (False → p3))) ∨ (((p6 → p2) ∨ (p4 ∨ p4)) ∨ ((p2 → False) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p3 p0 p6 p2 p4 p1 : Prop)
theorem file21_113266 : ((((((True ∨ p4) ∧ (p1 ∨ p1)) → ((p0 ∧ p1) ∧ (p3 → p2))) → False) ∧ ((((False ∧ p6) ∧ (True → p0)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((False ∧ p6) ∧ (True → p0)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p7 p3 p6 p0 p1 p5 p4 : Prop)
theorem file21_113850 : ((((((p1 ∧ p6) ∧ (False ∨ p5)) → ((False ∧ p3) → False)) ∨ (((p7 → p5) ∧ (p0 → p1)) → ((True ∧ p1) ∨ (p5 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p1 ∧ p6) ∧ (False ∨ p5)) → ((False ∧ p3) → False)) ∨ (((p7 → p5) ∧ (p0 → p1)) → ((True ∧ p1) ∨ (p5 ∨ p4)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p2 p0 p6 p7 p3 : Prop)
theorem file21_114409 : (((((p6 → False) ∨ (p3 ∨ p3)) → ((False ∧ p1) ∧ (p7 ∨ p7))) → (((False ∧ p3) → False) ∨ ((True → False) ∧ (p6 → p1)))) ∨ ((((p3 ∨ p0) ∧ (p1 ∧ p7)) ∧ ((p0 → p2) → (p6 ∧ p1))) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p2 p1 p3 p5 p0 p7 p6 : Prop)
theorem file21_114807 : (((((p5 ∨ True) ∨ (p2 ∨ p2)) → ((False → p0) ∧ (p5 → True))) ∨ (((p2 → p7) ∧ (p3 → False)) → ((False → False) → False))) ∨ ((((p0 ∨ p6) → False) ∨ ((p7 → p3) ∧ (p3 ∨ p1))) ∧ (((p5 ∨ p1) ∧ (True → p2)) → ((p3 ∧ p7) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  apply False.elim assump_2
  intro assump_5
  apply True.intro


variable (p1 p6 p4 p0 : Prop)
theorem file21_115239 : (((((p1 ∨ p4) ∨ (p0 → p0)) ∧ ((False → p6) ∨ (p4 ∧ False))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p1 ∨ p4) ∨ (p0 → p0)) ∧ ((False → p6) ∨ (p4 ∧ False))) := by
    apply And.intro
    apply Or.inr
    intro assump_5
    exact assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p4 p6 p1 p0 p5 p3 : Prop)
theorem file21_115692 : (((((p6 ∧ p3) → False) ∨ ((p2 → p0) ∧ (p4 ∨ p1))) ∧ (((p4 → True) → False) ∧ ((False → False) ∧ (p6 ∨ p5)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_13
          case inl assump_16 =>
            have assump_102 : (p4 → True) := by
              intro assump_23
              apply True.intro
            let assump_22 := assump_8 assump_102
            apply False.elim assump_22
          case inr assump_17 =>
            have assump_103 : (p4 → True) := by
              intro assump_32
              apply True.intro
            let assump_31 := assump_8 assump_103
            apply False.elim assump_31
    case inr assump_5 =>
      cases assump_5
      case intro assump_36 assump_37 =>
        cases assump_37
        case inl assump_40 =>
          cases assump_3
          case intro assump_44 assump_45 =>
            cases assump_45
            case intro assump_48 assump_49 =>
              cases assump_49
              case inl assump_52 =>
                have assump_104 : (p4 → True) := by
                  intro assump_59
                  apply True.intro
                let assump_58 := assump_44 assump_104
                apply False.elim assump_58
              case inr assump_53 =>
                have assump_105 : (p4 → True) := by
                  intro assump_68
                  apply True.intro
                let assump_67 := assump_44 assump_105
                apply False.elim assump_67
        case inr assump_41 =>
          cases assump_3
          case intro assump_74 assump_75 =>
            cases assump_75
            case intro assump_78 assump_79 =>
              cases assump_79
              case inl assump_82 =>
                have assump_106 : (p4 → True) := by
                  intro assump_89
                  apply True.intro
                let assump_88 := assump_74 assump_106
                apply False.elim assump_88
              case inr assump_83 =>
                have assump_107 : (p4 → True) := by
                  intro assump_98
                  apply True.intro
                let assump_97 := assump_74 assump_107
                apply False.elim assump_97


variable (p6 p5 p3 p0 p7 p2 p4 : Prop)
theorem file21_118131 : ((((((p7 → False) ∨ (p7 → p7)) → ((p0 ∧ p5) → False)) ∨ (((p3 → False) ∧ (p4 → False)) → False)) ∧ ((((p0 → p6) → (p4 → p0)) → False) ∧ (((p2 ∨ p5) ∧ (p5 → p4)) ∧ ((True ∨ p6) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              have assump_70 : (True ∨ p6) := by
                apply Or.inl
                apply True.intro
              let assump_24 := assump_13 assump_70
              apply False.elim assump_24
            case inr assump_17 =>
              have assump_71 : (True ∨ p6) := by
                apply Or.inl
                apply True.intro
              let assump_34 := assump_13 assump_71
              apply False.elim assump_34
    case inr assump_5 =>
      cases assump_3
      case intro assump_40 assump_41 =>
        cases assump_41
        case intro assump_44 assump_45 =>
          cases assump_44
          case intro assump_46 assump_47 =>
            cases assump_46
            case inl assump_48 =>
              have assump_72 : (True ∨ p6) := by
                apply Or.inl
                apply True.intro
              let assump_56 := assump_45 assump_72
              apply False.elim assump_56
            case inr assump_49 =>
              have assump_73 : (True ∨ p6) := by
                apply Or.inl
                apply True.intro
              let assump_66 := assump_45 assump_73
              apply False.elim assump_66


variable (p2 p5 p1 p0 p7 p3 p6 p4 : Prop)
theorem file21_119932 : ((((((True ∧ p6) ∧ (True ∧ p6)) ∧ ((p2 → p4) ∨ (False ∨ False))) ∧ (((p0 → p6) ∧ (p3 ∨ p4)) ∧ ((True → True) ∨ (p1 ∨ p7)))) ∧ ((((p6 ∧ False) ∧ (False ∨ p6)) ∧ ((p6 ∨ p0) → False)) ∧ (((True → False) ∨ (p2 ∨ False)) ∨ ((p1 ∨ True) ∧ (p2 ∨ p5))))) → False) := by
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
              case inl assump_22 =>
                cases assump_5
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    cases assump_29
                    case inl assump_32 =>
                      cases assump_27
                      case inl assump_36 =>
                        cases assump_3
                        case intro assump_40 assump_41 =>
                          cases assump_40
                          case intro assump_42 assump_43 =>
                            cases assump_42
                            case intro assump_44 assump_45 =>
                              cases assump_44
                              case intro assump_46 assump_47 =>
                                apply False.elim assump_47
                      case inr assump_37 =>
                        cases assump_37
                        case inl assump_52 =>
                          cases assump_3
                          case intro assump_56 assump_57 =>
                            cases assump_56
                            case intro assump_58 assump_59 =>
                              cases assump_58
                              case intro assump_60 assump_61 =>
                                cases assump_60
                                case intro assump_62 assump_63 =>
                                  apply False.elim assump_63
                        case inr assump_53 =>
                          cases assump_3
                          case intro assump_70 assump_71 =>
                            cases assump_70
                            case intro assump_72 assump_73 =>
                              cases assump_72
                              case intro assump_74 assump_75 =>
                                cases assump_74
                                case intro assump_76 assump_77 =>
                                  apply False.elim assump_77
                    case inr assump_33 =>
                      cases assump_27
                      case inl assump_84 =>
                        cases assump_3
                        case intro assump_88 assump_89 =>
                          cases assump_88
                          case intro assump_90 assump_91 =>
                            cases assump_90
                            case intro assump_92 assump_93 =>
                              cases assump_92
                              case intro assump_94 assump_95 =>
                                apply False.elim assump_95
                      case inr assump_85 =>
                        cases assump_85
                        case inl assump_100 =>
                          cases assump_3
                          case intro assump_104 assump_105 =>
                            cases assump_104
                            case intro assump_106 assump_107 =>
                              cases assump_106
                              case intro assump_108 assump_109 =>
                                cases assump_108
                                case intro assump_110 assump_111 =>
                                  apply False.elim assump_111
                        case inr assump_101 =>
                          cases assump_3
                          case intro assump_118 assump_119 =>
                            cases assump_118
                            case intro assump_120 assump_121 =>
                              cases assump_120
                              case intro assump_122 assump_123 =>
                                cases assump_122
                                case intro assump_124 assump_125 =>
                                  apply False.elim assump_125
              case inr assump_23 =>
                cases assump_23
                case inl assump_130 =>
                  apply False.elim assump_130
                case inr assump_131 =>
                  apply False.elim assump_131


variable (p4 p6 p5 p3 p7 p1 : Prop)
theorem file21_124689 : (((((p7 ∧ p1) → False) → False) → False) → ((((p1 ∧ p1) → False) → ((p7 → p7) ∧ (False → p4))) ∨ (((p3 ∨ p5) ∨ (p4 ∧ p7)) → ((p6 → False) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  intro assump_5
  exact assump_5
  intro assump_10
  apply False.elim assump_10


variable (p7 p0 p6 p5 p4 p3 p2 : Prop)
theorem file21_125056 : (((((p6 ∨ p2) ∨ (False → False)) → False) → False) ∨ ((((p3 → False) ∧ (p7 → p4)) → ((p4 ∧ p4) ∨ (p5 → p0))) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p6 ∨ p2) ∨ (False → False)) := by
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p5 p2 p1 : Prop)
theorem file21_125453 : ((((((p7 ∧ False) ∧ (p2 ∨ False)) ∧ ((p1 ∧ p2) → (False ∧ p5))) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p7 ∧ False) ∧ (p2 ∨ False)) ∧ ((p1 ∧ p2) → (False ∧ p5))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p2 p5 p0 p7 p6 p1 p4 p3 : Prop)
theorem file21_126029 : (((((True ∧ p5) ∨ (p3 → False)) ∧ ((p2 ∨ p1) ∨ (p2 → p6))) → (((p5 ∨ p0) → False) → ((p0 → False) ∨ (p6 ∧ p2)))) → ((((p6 → p4) → (p4 → False)) ∨ ((p2 → p2) → (p1 ∨ p1))) → (((p7 → False) → (False → p2)) ∨ ((p1 → p1) ∨ (p5 ∧ p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    intro assump_10
    apply False.elim assump_10
  case inr assump_4 =>
    apply Or.inl
    intro assump_17
    intro assump_18
    apply False.elim assump_18


variable (p5 p2 p0 p7 p3 p6 : Prop)
theorem file21_126600 : (((((p3 ∨ p5) → (p0 → p2)) → ((False ∨ p7) ∧ (p3 → False))) → (((p6 ∨ p0) ∨ (False → False)) ∨ ((p0 → False) → (p3 → False)))) ∨ ((((p6 ∧ False) → (p5 → False)) ∨ ((p5 ∨ p5) ∨ (p7 ∨ False))) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  apply False.elim assump_4


variable (p0 p6 p7 p3 p4 p2 : Prop)
theorem file21_126974 : (((((p2 ∧ p4) ∨ (True ∨ p2)) → ((p4 ∨ p7) → (p4 ∨ p6))) → False) → ((((p7 ∨ False) ∨ (p4 → False)) ∧ ((p7 ∨ p3) → (True ∨ p6))) ∧ (((p2 ∨ False) → (True ∧ True)) ∨ ((p2 → False) ∧ (p0 → False))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inr
  intro assump_4
  have assump_62 : (((p2 ∧ p4) ∨ (True ∨ p2)) → ((p4 ∨ p7) → (p4 ∨ p6))) := by
    intro assump_9
    intro assump_10
    cases assump_10
    case inl assump_11 =>
      cases assump_9
      case inl assump_15 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          apply Or.inl
          exact assump_18
      case inr assump_16 =>
        cases assump_16
        case inl assump_23 =>
          apply Or.inl
          exact assump_11
        case inr assump_24 =>
          apply Or.inl
          exact assump_11
    case inr assump_12 =>
      cases assump_9
      case inl assump_31 =>
        cases assump_31
        case intro assump_33 assump_34 =>
          apply Or.inl
          exact assump_34
      case inr assump_32 =>
        cases assump_32
        case inl assump_39 =>
          apply Or.inl
          exact assump_4
        case inr assump_40 =>
          apply Or.inl
          exact assump_4
  let assump_8 := assump_1 assump_62
  apply False.elim assump_8
  intro assump_48
  cases assump_48
  case inl assump_49 =>
    apply Or.inl
    apply True.intro
  case inr assump_50 =>
    apply Or.inl
    apply True.intro
  apply Or.inl
  intro assump_61
  apply And.intro
  apply True.intro
  apply True.intro


variable (p3 p4 p7 p1 p0 p6 : Prop)
theorem file21_128572 : (((((p6 → p7) → (p0 ∨ p0)) ∨ ((p4 ∧ p4) → (True ∨ p3))) → (((p0 → False) ∧ (p1 ∧ p3)) ∧ ((p1 → p4) ∧ (True ∨ p4)))) → ((((True ∧ p0) ∨ (p0 → p6)) ∨ ((False ∨ p3) → False)) ∨ (((p6 → True) → False) ∧ ((False → False) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_4
  have assump_18 : (((p6 → p7) → (p0 ∨ p0)) ∨ ((p4 ∧ p4) → (True ∨ p3))) := by
    apply Or.inl
    intro assump_9
    apply Or.inl
    exact assump_4
  let assump_8 := assump_1 assump_18
  let assump_12 := And.left assump_8
  let assump_13 := And.left assump_12
  have assump_19 : p0 := by
    exact assump_4
  let assump_14 := assump_13 assump_19
  apply False.elim assump_14


variable (p1 p6 p7 p4 p5 p0 p3 p2 : Prop)
theorem file21_129329 : ((((((p1 → p6) ∨ (p0 ∧ p0)) ∧ ((False ∧ p2) → False)) ∧ (((p3 → False) → (p4 ∨ True)) ∧ ((p4 ∧ p1) ∧ (p0 ∧ False)))) ∧ ((((False ∧ p5) → (p5 → p7)) → ((p3 → False) ∨ (True → p6))) ∨ (((False → p6) ∨ (p0 ∧ p6)) ∨ ((True ∨ True) ∧ (p3 ∨ p3))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_19
                case intro assump_26 assump_27 =>
                  apply False.elim assump_27
        case inr assump_9 =>
          cases assump_9
          case intro assump_32 assump_33 =>
            cases assump_5
            case intro assump_40 assump_41 =>
              cases assump_41
              case intro assump_44 assump_45 =>
                cases assump_44
                case intro assump_46 assump_47 =>
                  cases assump_45
                  case intro assump_52 assump_53 =>
                    apply False.elim assump_53


variable (p4 p2 p6 p1 p7 p5 p0 p3 : Prop)
theorem file21_130699 : ((((((p6 → p1) ∧ (p3 ∨ False)) ∧ ((p6 ∧ p5) ∧ (p1 → False))) ∨ (((False ∨ p1) → (False ∨ p0)) ∨ ((p5 → p2) ∨ (p2 → False)))) ∧ ((((p1 → False) ∧ (p6 ∨ p6)) → ((p3 ∧ p5) ∧ (p0 ∧ p5))) ∧ (((False → p6) → False) ∧ ((p7 → p7) ∧ (False ∧ p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case inl assump_12 =>
            cases assump_7
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_3
                case intro assump_26 assump_27 =>
                  cases assump_27
                  case intro assump_30 assump_31 =>
                    cases assump_31
                    case intro assump_34 assump_35 =>
                      cases assump_35
                      case intro assump_38 assump_39 =>
                        apply False.elim assump_38
          case inr assump_13 =>
            apply False.elim assump_13
    case inr assump_5 =>
      cases assump_5
      case inl assump_44 =>
        cases assump_3
        case intro assump_48 assump_49 =>
          cases assump_49
          case intro assump_52 assump_53 =>
            cases assump_53
            case intro assump_56 assump_57 =>
              cases assump_57
              case intro assump_60 assump_61 =>
                apply False.elim assump_60
      case inr assump_45 =>
        cases assump_45
        case inl assump_64 =>
          cases assump_3
          case intro assump_68 assump_69 =>
            cases assump_69
            case intro assump_72 assump_73 =>
              cases assump_73
              case intro assump_76 assump_77 =>
                cases assump_77
                case intro assump_80 assump_81 =>
                  apply False.elim assump_80
        case inr assump_65 =>
          cases assump_3
          case intro assump_86 assump_87 =>
            cases assump_87
            case intro assump_90 assump_91 =>
              cases assump_91
              case intro assump_94 assump_95 =>
                cases assump_95
                case intro assump_98 assump_99 =>
                  apply False.elim assump_98


variable (p5 p3 p0 p1 p6 p2 p4 p7 : Prop)
theorem file21_133148 : ((((((True ∨ p4) ∨ (p0 ∨ True)) → ((p5 ∧ True) → (p2 ∧ p4))) ∨ (((p1 ∧ True) ∧ (p0 ∨ p4)) → ((p3 → p7) ∧ (p6 → False)))) ∧ ((((True ∧ True) ∨ (p6 ∧ p1)) → ((True → False) ∧ (False → False))) ∧ (((p5 → False) ∨ (p7 ∧ p2)) ∨ ((p4 ∧ p6) ∨ (p5 ∧ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_12
          case inl assump_14 =>
            have assump_132 : ((True ∧ True) ∨ (p6 ∧ p1)) := by
              apply Or.inl
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_19 := assump_8 assump_132
            let assump_20 := And.left assump_19
            have assump_133 : True := by
              apply True.intro
            let assump_21 := assump_20 assump_133
            apply False.elim assump_21
          case inr assump_15 =>
            cases assump_15
            case intro assump_25 assump_26 =>
              have assump_134 : ((True ∧ True) ∨ (p6 ∧ p1)) := by
                apply Or.inl
                apply And.intro
                apply True.intro
                apply True.intro
              let assump_33 := assump_8 assump_134
              let assump_34 := And.left assump_33
              have assump_135 : True := by
                apply True.intro
              let assump_35 := assump_34 assump_135
              apply False.elim assump_35
        case inr assump_13 =>
          cases assump_13
          case inl assump_39 =>
            cases assump_39
            case intro assump_41 assump_42 =>
              have assump_136 : ((True ∧ True) ∨ (p6 ∧ p1)) := by
                apply Or.inl
                apply And.intro
                apply True.intro
                apply True.intro
              let assump_49 := assump_8 assump_136
              let assump_50 := And.left assump_49
              have assump_137 : True := by
                apply True.intro
              let assump_51 := assump_50 assump_137
              apply False.elim assump_51
          case inr assump_40 =>
            cases assump_40
            case intro assump_55 assump_56 =>
              have assump_138 : ((True ∧ True) ∨ (p6 ∧ p1)) := by
                apply Or.inl
                apply And.intro
                apply True.intro
                apply True.intro
              let assump_63 := assump_8 assump_138
              let assump_64 := And.left assump_63
              have assump_139 : True := by
                apply True.intro
              let assump_65 := assump_64 assump_139
              apply False.elim assump_65
    case inr assump_5 =>
      cases assump_3
      case intro assump_71 assump_72 =>
        cases assump_72
        case inl assump_75 =>
          cases assump_75
          case inl assump_77 =>
            have assump_140 : ((True ∧ True) ∨ (p6 ∧ p1)) := by
              apply Or.inl
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_82 := assump_71 assump_140
            let assump_83 := And.left assump_82
            have assump_141 : True := by
              apply True.intro
            let assump_84 := assump_83 assump_141
            apply False.elim assump_84
          case inr assump_78 =>
            cases assump_78
            case intro assump_88 assump_89 =>
              have assump_142 : ((True ∧ True) ∨ (p6 ∧ p1)) := by
                apply Or.inl
                apply And.intro
                apply True.intro
                apply True.intro
              let assump_96 := assump_71 assump_142
              let assump_97 := And.left assump_96
              have assump_143 : True := by
                apply True.intro
              let assump_98 := assump_97 assump_143
              apply False.elim assump_98
        case inr assump_76 =>
          cases assump_76
          case inl assump_102 =>
            cases assump_102
            case intro assump_104 assump_105 =>
              have assump_144 : ((True ∧ True) ∨ (p6 ∧ p1)) := by
                apply Or.inl
                apply And.intro
                apply True.intro
                apply True.intro
              let assump_112 := assump_71 assump_144
              let assump_113 := And.left assump_112
              have assump_145 : True := by
                apply True.intro
              let assump_114 := assump_113 assump_145
              apply False.elim assump_114
          case inr assump_103 =>
            cases assump_103
            case intro assump_118 assump_119 =>
              have assump_146 : ((True ∧ True) ∨ (p6 ∧ p1)) := by
                apply Or.inl
                apply And.intro
                apply True.intro
                apply True.intro
              let assump_126 := assump_71 assump_146
              let assump_127 := And.left assump_126
              have assump_147 : True := by
                apply True.intro
              let assump_128 := assump_127 assump_147
              apply False.elim assump_128


variable (p2 p6 p3 p4 p0 : Prop)
theorem file21_138382 : ((((((p0 ∧ p3) → (p4 ∨ p0)) → False) → (((p6 ∨ p0) → False) ∨ ((p2 → p6) ∧ (p3 → False)))) → False) → False) := by
  intro assump_13
  have assump_54 : ((((p0 ∧ p3) → (p4 ∨ p0)) → False) → (((p6 ∨ p0) → False) ∨ ((p2 → p6) ∧ (p3 → False)))) := by
    intro assump_17
    apply Or.inl
    intro assump_20
    cases assump_20
    case inl assump_21 =>
      have assump_55 : ((p0 ∧ p3) → (p4 ∨ p0)) := by
        intro assump_27
        cases assump_27
        case intro assump_28 assump_29 =>
          apply Or.inr
          exact assump_28
      let assump_26 := assump_17 assump_55
      apply False.elim assump_26
    case inr assump_22 =>
      have assump_56 : ((p0 ∧ p3) → (p4 ∨ p0)) := by
        intro assump_41
        cases assump_41
        case intro assump_42 assump_43 =>
          apply Or.inr
          exact assump_42
      let assump_40 := assump_17 assump_56
      apply False.elim assump_40
  let assump_16 := assump_13 assump_54
  apply False.elim assump_16


variable (p4 p5 p1 p2 p3 : Prop)
theorem file21_139419 : ((((((p1 ∨ p2) ∧ (p5 ∧ False)) → ((True ∧ p4) → (False ∧ True))) ∨ (((p5 ∧ p3) → (p2 → False)) → False)) → False) → False) := by
  intro assump_9
  have assump_44 : ((((p1 ∨ p2) ∧ (p5 ∧ False)) → ((True ∧ p4) → (False ∧ True))) ∨ (((p5 ∧ p3) → (p2 → False)) → False)) := by
    apply Or.inl
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
            apply False.elim assump_28
        case inr assump_24 =>
          cases assump_22
          case intro assump_35 assump_36 =>
            apply False.elim assump_36
    apply True.intro
  let assump_12 := assump_9 assump_44
  apply False.elim assump_12


