variable (p5 p3 p6 p0 p4 : Prop)
theorem file93_41 : (((((p6 → False) ∧ (p0 ∨ p3)) ∧ ((p4 ∨ p4) → (p4 → False))) ∨ (((p3 ∧ p5) → (p6 ∨ p0)) ∧ ((False ∨ p4) → False))) → ((((True → True) ∨ (p4 ∨ p4)) → ((False → p3) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_10
        case inl assump_13 =>
          have assump_64 : ((True → True) ∨ (p4 ∨ p4)) := by
            apply Or.inl
            intro assump_23
            apply True.intro
          let assump_22 := assump_2 assump_64
          have assump_65 : (False → p3) := by
            intro assump_25
            apply False.elim assump_25
          let assump_24 := assump_22 assump_65
          apply False.elim assump_24
        case inr assump_14 =>
          have assump_66 : ((True → True) ∨ (p4 ∨ p4)) := by
            apply Or.inl
            intro assump_39
            apply True.intro
          let assump_38 := assump_2 assump_66
          have assump_67 : (False → p3) := by
            intro assump_41
            apply False.elim assump_41
          let assump_40 := assump_38 assump_67
          apply False.elim assump_40
  case inr assump_6 =>
    cases assump_6
    case intro assump_47 assump_48 =>
      have assump_68 : ((True → True) ∨ (p4 ∨ p4)) := by
        apply Or.inl
        intro assump_56
        apply True.intro
      let assump_55 := assump_2 assump_68
      have assump_69 : (False → p3) := by
        intro assump_58
        apply False.elim assump_58
      let assump_57 := assump_55 assump_69
      apply False.elim assump_57


variable (p4 p0 p3 p5 : Prop)
theorem file93_1754 : (((((False → False) ∨ (p5 → p4)) ∨ ((p0 → p3) → False)) → False) → False) := by
  intro assump_39
  have assump_49 : (((False → False) ∨ (p5 → p4)) ∨ ((p0 → p3) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_43
    apply False.elim assump_43
  let assump_42 := assump_39 assump_49
  apply False.elim assump_42


variable (p2 p5 p3 p4 p1 : Prop)
theorem file93_2141 : ((((((False → False) ∨ (p3 ∧ p1)) ∨ ((p4 ∧ p5) → False)) → False) ∧ ((((p3 ∧ p1) ∨ (False ∧ False)) ∧ ((p3 ∧ p4) ∨ (True ∨ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((False → False) ∨ (p3 ∧ p1)) ∨ ((p4 ∧ p5) → False)) := by
      apply Or.inl
      apply Or.inl
      intro assump_10
      apply False.elim assump_10
    let assump_9 := assump_2 assump_16
    apply False.elim assump_9


variable (p0 p5 p7 p2 p3 p4 p1 p6 : Prop)
theorem file93_2672 : (((((False → True) ∧ (p2 ∨ p7)) ∨ ((p5 → True) ∧ (p5 ∧ p5))) ∧ (((p1 ∧ p0) → (p6 → p4)) ∨ ((p7 → False) ∧ (p4 ∨ p5)))) → ((((False → False) → False) ∧ ((p3 ∨ p7) ∧ (p4 ∧ False))) → (((False ∨ p6) ∧ (p5 → p4)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case inl assump_6 =>
      apply False.elim assump_6
    case inr assump_7 =>
      cases assump_2
      case intro assump_14 assump_15 =>
        cases assump_15
        case intro assump_18 assump_19 =>
          cases assump_18
          case inl assump_20 =>
            cases assump_19
            case intro assump_24 assump_25 =>
              apply False.elim assump_25
          case inr assump_21 =>
            cases assump_19
            case intro assump_32 assump_33 =>
              apply False.elim assump_33


variable (p1 p6 p7 p2 : Prop)
theorem file93_3602 : (((((False ∧ p6) → (p7 → p2)) → False) ∧ (((False → False) ∨ (p6 ∧ p1)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((False → False) ∨ (p6 ∧ p1)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p5 p6 p4 p1 p0 : Prop)
theorem file93_4022 : (((((p0 → p1) → (True ∨ True)) ∧ ((True ∧ True) ∨ (p0 → False))) ∨ (((p1 ∧ p5) ∧ (p4 → False)) → False)) ∨ ((((p4 → p5) → (False → False)) ∧ ((p6 ∨ True) → False)) → (((p5 ∧ p4) → False) ∨ ((True ∨ p0) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_1
  apply Or.inl
  apply True.intro
  apply Or.inl
  apply And.intro
  apply True.intro
  apply True.intro


variable (p4 p3 p1 p5 p2 p0 p6 p7 : Prop)
theorem file93_4478 : (((((p0 ∧ p5) ∧ (p6 ∧ p0)) → ((p5 ∧ p4) ∨ (p6 ∧ p5))) → (((p1 → p0) ∧ (True → False)) → False)) ∨ ((((True → p1) ∨ (p2 ∨ p2)) ∨ ((p0 ∧ p1) → (p6 → p0))) → (((p3 → p1) ∧ (p6 ∨ p7)) ∨ ((False → False) ∨ (p4 → False))))) := by
  apply Or.inl
  intro assump_11
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    have assump_26 : True := by
      apply True.intro
    let assump_22 := assump_14 assump_26
    apply False.elim assump_22


variable (p1 p3 p7 p5 p2 p4 p0 p6 : Prop)
theorem file93_5000 : ((((((p2 → False) ∧ (p2 ∧ p6)) → ((p2 ∨ p4) → False)) ∨ (((p3 → p7) ∧ (False → False)) ∨ ((p4 → False) ∧ (p7 ∨ p3)))) → ((((p0 ∨ p1) ∧ (p5 → False)) → ((p6 ∨ False) ∨ (p7 → False))) ∧ (((True → False) → (p4 → False)) → False))) → False) := by
  intro assump_1
  have assump_61 : ((((p2 → False) ∧ (p2 ∧ p6)) → ((p2 ∨ p4) → False)) ∨ (((p3 → p7) ∧ (False → False)) ∨ ((p4 → False) ∧ (p7 ∨ p3)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          have assump_62 : p2 := by
            exact assump_15
          let assump_23 := assump_11 assump_62
          apply False.elim assump_23
    case inr assump_8 =>
      cases assump_5
      case intro assump_29 assump_30 =>
        cases assump_30
        case intro assump_33 assump_34 =>
          have assump_63 : p2 := by
            exact assump_33
          let assump_41 := assump_29 assump_63
          apply False.elim assump_41
  let assump_4 := assump_1 assump_61
  let assump_45 := And.right assump_4
  have assump_64 : ((True → False) → (p4 → False)) := by
    intro assump_48
    intro assump_49
    have assump_65 : True := by
      apply True.intro
    let assump_54 := assump_48 assump_65
    apply False.elim assump_54
  let assump_47 := assump_45 assump_64
  apply False.elim assump_47


variable (p7 p1 p2 p4 p5 p3 p6 : Prop)
theorem file93_6505 : (((((p6 → p6) ∧ (p7 → False)) ∧ ((p6 ∧ p7) ∧ (False ∨ p5))) → False) ∧ ((((p1 → p1) ∨ (p3 → False)) ∨ ((p4 → False) ∨ (True ∨ p6))) ∨ (((p3 ∧ p6) ∧ (p6 → p2)) → False))) := by
  apply And.intro
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_16
      case intro assump_23 assump_24 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          cases assump_24
          case inl assump_31 =>
            apply False.elim assump_31
          case inr assump_32 =>
            have assump_47 : p7 := by
              exact assump_26
            let assump_40 := assump_18 assump_47
            apply False.elim assump_40
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_44
  exact assump_44


variable (p7 p5 p6 p1 p0 p4 p3 : Prop)
theorem file93_7386 : (((((p1 → p4) → (p3 ∧ p5)) ∨ ((p4 ∧ p4) ∨ (p5 ∨ p0))) ∧ (((p3 ∨ p7) ∧ (True → False)) ∧ ((False ∧ p7) → False))) → ((((p6 → p4) ∧ (p7 → p6)) → ((p0 → False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_13
          case inl assump_15 =>
            have assump_137 : True := by
              apply True.intro
            let assump_24 := assump_14 assump_137
            apply False.elim assump_24
          case inr assump_16 =>
            have assump_138 : True := by
              apply True.intro
            let assump_35 := assump_14 assump_138
            apply False.elim assump_35
    case inr assump_8 =>
      cases assump_8
      case inl assump_39 =>
        cases assump_39
        case intro assump_41 assump_42 =>
          cases assump_6
          case intro assump_47 assump_48 =>
            cases assump_47
            case intro assump_49 assump_50 =>
              cases assump_49
              case inl assump_51 =>
                have assump_139 : True := by
                  apply True.intro
                let assump_60 := assump_50 assump_139
                apply False.elim assump_60
              case inr assump_52 =>
                have assump_140 : True := by
                  apply True.intro
                let assump_71 := assump_50 assump_140
                apply False.elim assump_71
      case inr assump_40 =>
        cases assump_40
        case inl assump_75 =>
          cases assump_6
          case intro assump_79 assump_80 =>
            cases assump_79
            case intro assump_81 assump_82 =>
              cases assump_81
              case inl assump_83 =>
                have assump_141 : True := by
                  apply True.intro
                let assump_92 := assump_82 assump_141
                apply False.elim assump_92
              case inr assump_84 =>
                have assump_142 : True := by
                  apply True.intro
                let assump_103 := assump_82 assump_142
                apply False.elim assump_103
        case inr assump_76 =>
          cases assump_6
          case intro assump_109 assump_110 =>
            cases assump_109
            case intro assump_111 assump_112 =>
              cases assump_111
              case inl assump_113 =>
                have assump_143 : True := by
                  apply True.intro
                let assump_122 := assump_112 assump_143
                apply False.elim assump_122
              case inr assump_114 =>
                have assump_144 : True := by
                  apply True.intro
                let assump_133 := assump_112 assump_144
                apply False.elim assump_133


variable (p0 p4 p5 p7 p3 p1 p6 : Prop)
theorem file93_10365 : (((((p6 ∧ p3) → (p0 ∧ p7)) → False) ∨ (((p4 → False) ∧ (True ∧ p7)) ∧ ((True → False) ∨ (p7 → p1)))) → ((((p5 ∨ p3) → (p1 → False)) → ((True ∧ False) → False)) ∨ (((p4 ∨ p3) ∨ (p0 → False)) ∨ ((p3 ∨ p6) → (p4 → p5))))) := by
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    apply Or.inl
    intro assump_10
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      apply False.elim assump_13
  case inr assump_7 =>
    cases assump_7
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        cases assump_21
        case intro assump_24 assump_25 =>
          cases assump_19
          case inl assump_30 =>
            apply Or.inl
            intro assump_34
            intro assump_35
            cases assump_35
            case intro assump_36 assump_37 =>
              apply False.elim assump_37
          case inr assump_31 =>
            apply Or.inl
            intro assump_44
            intro assump_45
            cases assump_45
            case intro assump_46 assump_47 =>
              apply False.elim assump_47


variable (p2 p7 p1 p0 p5 p3 p6 p4 : Prop)
theorem file93_11551 : (((((p7 → False) ∧ (False → False)) → ((p7 → False) ∨ (p3 ∧ False))) → (((p1 ∨ p0) → (True ∨ p2)) → ((p6 → p3) → (p3 → p5)))) → ((((True → False) → (p4 ∨ p4)) ∧ ((False ∧ p6) → (p4 → False))) ∨ (((p7 ∨ p1) → False) ∨ ((p7 ∨ p0) ∧ (p7 ∨ False))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_19 : True := by
    apply True.intro
  let assump_7 := assump_4 assump_19
  apply False.elim assump_7
  intro assump_11
  intro assump_12
  cases assump_11
  case intro assump_15 assump_16 =>
    apply False.elim assump_15


variable (p6 p5 p1 p7 p4 p2 p3 : Prop)
theorem file93_12171 : (((((False ∧ p3) ∧ (p1 → False)) ∨ ((p1 ∧ True) → False)) ∧ (((p2 → True) → False) ∨ ((p6 → False) ∧ (p7 ∨ p6)))) → ((((True ∧ p5) → False) ∨ ((True ∧ p4) ∧ (p6 → False))) → (((p3 ∧ False) → (p3 ∧ p4)) ∨ ((p5 → False) ∧ (p1 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_11
          case intro assump_13 assump_14 =>
            apply False.elim assump_13
      case inr assump_10 =>
        cases assump_8
        case inl assump_19 =>
          apply Or.inl
          intro assump_23
          apply And.intro
          cases assump_23
          case intro assump_24 assump_25 =>
            apply False.elim assump_25
          cases assump_23
          case intro assump_30 assump_31 =>
            apply False.elim assump_31
        case inr assump_20 =>
          cases assump_20
          case intro assump_36 assump_37 =>
            cases assump_37
            case inl assump_40 =>
              apply Or.inl
              intro assump_44
              apply And.intro
              cases assump_44
              case intro assump_45 assump_46 =>
                apply False.elim assump_46
              cases assump_44
              case intro assump_51 assump_52 =>
                apply False.elim assump_52
            case inr assump_41 =>
              apply Or.inl
              intro assump_59
              apply And.intro
              cases assump_59
              case intro assump_60 assump_61 =>
                apply False.elim assump_61
              cases assump_59
              case intro assump_66 assump_67 =>
                apply False.elim assump_67
  case inr assump_4 =>
    cases assump_4
    case intro assump_72 assump_73 =>
      cases assump_72
      case intro assump_74 assump_75 =>
        cases assump_1
        case intro assump_82 assump_83 =>
          cases assump_82
          case inl assump_84 =>
            cases assump_84
            case intro assump_86 assump_87 =>
              cases assump_86
              case intro assump_88 assump_89 =>
                apply False.elim assump_88
          case inr assump_85 =>
            cases assump_83
            case inl assump_94 =>
              apply Or.inl
              intro assump_98
              apply And.intro
              cases assump_98
              case intro assump_99 assump_100 =>
                apply False.elim assump_100
              cases assump_98
              case intro assump_105 assump_106 =>
                apply False.elim assump_106
            case inr assump_95 =>
              cases assump_95
              case intro assump_111 assump_112 =>
                cases assump_112
                case inl assump_115 =>
                  apply Or.inl
                  intro assump_119
                  apply And.intro
                  cases assump_119
                  case intro assump_120 assump_121 =>
                    apply False.elim assump_121
                  cases assump_119
                  case intro assump_126 assump_127 =>
                    apply False.elim assump_127
                case inr assump_116 =>
                  apply Or.inl
                  intro assump_134
                  apply And.intro
                  cases assump_134
                  case intro assump_135 assump_136 =>
                    apply False.elim assump_136
                  cases assump_134
                  case intro assump_141 assump_142 =>
                    apply False.elim assump_142


variable (p3 p5 p2 p1 p0 p7 p6 p4 : Prop)
theorem file93_15920 : (((((True ∧ p3) → (p6 → p6)) ∨ ((p4 ∧ p0) ∧ (p5 → False))) ∨ (((p0 → False) ∧ (p5 ∨ p3)) → ((p1 ∧ p2) → (p5 → p6)))) ∨ ((((p4 → False) → (False → False)) → False) ∧ (((p7 → False) ∨ (p7 → p3)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    exact assump_2


variable (p7 p0 p5 p4 p3 p1 p6 p2 : Prop)
theorem file93_16345 : (((((False ∧ p2) ∨ (p3 → p7)) ∧ ((p5 → p1) → (p0 → False))) ∧ (((True → False) → (p6 ∧ True)) → False)) → ((((p4 ∧ False) ∨ (False → p0)) → False) → (((p2 ∧ p2) ∨ (p0 ∧ p4)) ∨ ((False → False) ∧ (False ∧ False))))) := by
  intro assump_15
  intro assump_16
  cases assump_15
  case intro assump_19 assump_20 =>
    cases assump_19
    case intro assump_21 assump_22 =>
      cases assump_21
      case inl assump_23 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          apply False.elim assump_25
      case inr assump_24 =>
        have assump_49 : ((True → False) → (p6 ∧ True)) := by
          intro assump_39
          apply And.intro
          have assump_50 : True := by
            apply True.intro
          let assump_42 := assump_39 assump_50
          apply False.elim assump_42
          apply True.intro
        let assump_38 := assump_20 assump_49
        apply False.elim assump_38


variable (p4 p7 p2 p6 : Prop)
theorem file93_17321 : (((((True → p4) ∨ (p6 ∨ False)) → False) ∧ (((False ∧ False) ∧ (True ∨ p6)) ∧ ((p7 → p2) → False))) → False) := by
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


variable (p2 p0 : Prop)
theorem file93_17768 : ((((((p2 ∨ True) → False) → False) ∨ (((p0 ∨ False) ∧ (True ∨ p0)) → ((True ∨ p2) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p2 ∨ True) → False) → False) ∨ (((p0 ∨ False) ∧ (True ∨ p0)) → ((True ∨ p2) → False))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (p2 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p6 p1 p4 p0 p2 p5 : Prop)
theorem file93_18332 : (((((False → False) → (p1 ∨ False)) ∨ ((p6 ∧ p7) ∨ (p5 ∧ True))) ∧ (((p1 ∨ True) ∨ (True ∧ p7)) ∧ ((False → False) → False))) → ((((True ∨ p2) ∨ (p0 → p4)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_13
          case inl assump_15 =>
            have assump_154 : (False → False) := by
              intro assump_22
              apply False.elim assump_22
            let assump_21 := assump_12 assump_154
            apply False.elim assump_21
          case inr assump_16 =>
            have assump_155 : (False → False) := by
              intro assump_33
              apply False.elim assump_33
            let assump_32 := assump_12 assump_155
            apply False.elim assump_32
        case inr assump_14 =>
          cases assump_14
          case intro assump_39 assump_40 =>
            have assump_156 : (False → False) := by
              intro assump_48
              apply False.elim assump_48
            let assump_47 := assump_12 assump_156
            apply False.elim assump_47
    case inr assump_8 =>
      cases assump_8
      case inl assump_54 =>
        cases assump_54
        case intro assump_56 assump_57 =>
          cases assump_6
          case intro assump_62 assump_63 =>
            cases assump_62
            case inl assump_64 =>
              cases assump_64
              case inl assump_66 =>
                have assump_157 : (False → False) := by
                  intro assump_73
                  apply False.elim assump_73
                let assump_72 := assump_63 assump_157
                apply False.elim assump_72
              case inr assump_67 =>
                have assump_158 : (False → False) := by
                  intro assump_84
                  apply False.elim assump_84
                let assump_83 := assump_63 assump_158
                apply False.elim assump_83
            case inr assump_65 =>
              cases assump_65
              case intro assump_90 assump_91 =>
                have assump_159 : (False → False) := by
                  intro assump_99
                  apply False.elim assump_99
                let assump_98 := assump_63 assump_159
                apply False.elim assump_98
      case inr assump_55 =>
        cases assump_55
        case intro assump_105 assump_106 =>
          cases assump_6
          case intro assump_111 assump_112 =>
            cases assump_111
            case inl assump_113 =>
              cases assump_113
              case inl assump_115 =>
                have assump_160 : (False → False) := by
                  intro assump_122
                  apply False.elim assump_122
                let assump_121 := assump_112 assump_160
                apply False.elim assump_121
              case inr assump_116 =>
                have assump_161 : (False → False) := by
                  intro assump_133
                  apply False.elim assump_133
                let assump_132 := assump_112 assump_161
                apply False.elim assump_132
            case inr assump_114 =>
              cases assump_114
              case intro assump_139 assump_140 =>
                have assump_162 : (False → False) := by
                  intro assump_148
                  apply False.elim assump_148
                let assump_147 := assump_112 assump_162
                apply False.elim assump_147


variable (p3 p0 : Prop)
theorem file93_21975 : ((((((True → False) → (p3 ∨ False)) → ((True → False) ∧ (p0 ∨ True))) → False) → False) → False) := by
  intro assump_1
  have assump_24 : ((((True → False) → (p3 ∨ False)) → ((True → False) ∧ (p0 ∨ True))) → False) := by
    intro assump_5
    have assump_25 : ((True → False) → (p3 ∨ False)) := by
      intro assump_9
      have assump_26 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_26
      apply False.elim assump_12
    let assump_8 := assump_5 assump_25
    let assump_16 := And.left assump_8
    have assump_27 : True := by
      apply True.intro
    let assump_17 := assump_16 assump_27
    apply False.elim assump_17
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p3 p5 p4 p1 p6 p2 p7 : Prop)
theorem file93_22763 : (((((p6 ∧ p3) ∨ (p4 → False)) ∨ ((False ∨ p2) ∧ (p7 ∨ False))) → False) → ((((p6 ∧ p5) → (p6 ∧ p1)) ∨ ((p3 → False) → (p3 → False))) → (((False ∧ False) ∧ (p7 ∨ p5)) ∨ ((p4 → False) → (p3 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inr
    intro assump_9
    intro assump_10
    have assump_53 : (((p6 ∧ p3) ∨ (p4 → False)) ∨ ((False ∨ p2) ∧ (p7 ∨ False))) := by
      apply Or.inl
      apply Or.inr
      intro assump_18
      have assump_54 : p4 := by
        exact assump_18
      let assump_22 := assump_9 assump_54
      apply False.elim assump_22
    let assump_17 := assump_1 assump_53
    apply False.elim assump_17
  case inr assump_4 =>
    apply Or.inr
    intro assump_33
    intro assump_34
    have assump_55 : (((p6 ∧ p3) ∨ (p4 → False)) ∨ ((False ∨ p2) ∧ (p7 ∨ False))) := by
      apply Or.inl
      apply Or.inr
      intro assump_42
      have assump_56 : p4 := by
        exact assump_42
      let assump_46 := assump_33 assump_56
      apply False.elim assump_46
    let assump_41 := assump_1 assump_55
    apply False.elim assump_41


variable (p6 p4 p1 p0 p3 p2 : Prop)
theorem file93_23941 : (((((p6 → False) → False) ∨ ((p0 → False) → False)) → (((p0 ∧ p1) ∨ (True ∨ p1)) ∨ ((p4 ∧ True) ∧ (p3 → True)))) ∨ ((((p3 ∧ p2) ∨ (p4 → False)) → False) ∨ (((p6 ∧ p2) ∨ (True → True)) ∧ ((True → p1) → (p3 ∨ p2))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro


variable (p7 p2 p3 p1 p5 p6 : Prop)
theorem file93_24461 : (((((p7 ∧ False) → False) ∨ ((p6 → p3) ∧ (p7 → p1))) → False) → ((((p2 ∧ p2) → (True → False)) ∧ ((True → False) → False)) ∧ (((p6 ∨ p1) → (p5 → False)) → ((False → False) ∨ (p3 ∨ p7))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    have assump_49 : (((p7 ∧ False) → False) ∨ ((p6 → p3) ∧ (p7 → p1))) := by
      apply Or.inl
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        apply False.elim assump_17
    let assump_14 := assump_1 assump_49
    apply False.elim assump_14
  intro assump_25
  have assump_50 : (((p7 ∧ False) → False) ∨ ((p6 → p3) ∧ (p7 → p1))) := by
    apply Or.inl
    intro assump_31
    cases assump_31
    case intro assump_32 assump_33 =>
      apply False.elim assump_33
  let assump_30 := assump_1 assump_50
  apply False.elim assump_30
  intro assump_41
  apply Or.inl
  intro assump_46
  apply False.elim assump_46


variable (p0 : Prop)
theorem file93_25494 : ((((((False ∧ p0) → False) → False) → False) → False) → False) := by
  intro assump_6
  have assump_25 : ((((False ∧ p0) → False) → False) → False) := by
    intro assump_10
    have assump_26 : ((False ∧ p0) → False) := by
      intro assump_14
      cases assump_14
      case intro assump_15 assump_16 =>
        apply False.elim assump_15
    let assump_13 := assump_10 assump_26
    apply False.elim assump_13
  let assump_9 := assump_6 assump_25
  apply False.elim assump_9


variable (p7 p2 p0 p1 p6 : Prop)
theorem file93_26031 : ((((((p6 ∧ False) ∧ (p1 → False)) ∧ ((p6 ∧ False) ∨ (True → False))) ∧ (((False → p1) ∧ (p2 ∨ p2)) ∨ ((p1 → True) → False))) ∧ ((((p2 ∧ p6) ∨ (False → p6)) → ((p6 ∧ p6) → (p7 → False))) → (((False ∧ p6) ∨ (p6 ∨ p0)) → ((p2 → False) ∨ (True → False))))) → False) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_13
    case intro assump_15 assump_16 =>
      cases assump_15
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          cases assump_19
          case intro assump_21 assump_22 =>
            apply False.elim assump_22


variable (p2 p6 p7 p1 p4 p3 : Prop)
theorem file93_26726 : ((((((p3 ∧ p6) ∧ (p6 → False)) ∧ ((p4 → p3) ∧ (p1 → p6))) ∨ (((p7 → True) → False) → ((p6 → False) ∧ (p2 → False)))) → False) → False) := by
  intro assump_23
  have assump_51 : ((((p3 ∧ p6) ∧ (p6 → False)) ∧ ((p4 → p3) ∧ (p1 → p6))) ∨ (((p7 → True) → False) → ((p6 → False) ∧ (p2 → False)))) := by
    apply Or.inr
    intro assump_27
    apply And.intro
    intro assump_28
    have assump_52 : (p7 → True) := by
      intro assump_34
      apply True.intro
    let assump_33 := assump_27 assump_52
    apply False.elim assump_33
    intro assump_38
    have assump_53 : (p7 → True) := by
      intro assump_44
      apply True.intro
    let assump_43 := assump_27 assump_53
    apply False.elim assump_43
  let assump_26 := assump_23 assump_51
  apply False.elim assump_26


variable (p1 p5 p0 p4 p7 p6 p2 p3 : Prop)
theorem file93_27568 : ((((((p5 ∨ p1) → False) ∨ ((p4 ∧ p6) → (p3 → False))) → (((p4 ∧ p7) → (p0 → p1)) ∨ ((False ∧ p7) → (p0 → False)))) ∧ ((((p5 → p2) → (p1 → p5)) ∨ ((True → False) → (p6 → p1))) ∧ (((p6 → p7) ∨ (p6 ∧ p2)) ∧ ((p1 → p1) → False)))) → False) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_14
    case intro assump_17 assump_18 =>
      cases assump_17
      case inl assump_19 =>
        cases assump_18
        case intro assump_23 assump_24 =>
          cases assump_23
          case inl assump_25 =>
            have assump_85 : (p1 → p1) := by
              intro assump_32
              exact assump_32
            let assump_31 := assump_24 assump_85
            apply False.elim assump_31
          case inr assump_26 =>
            cases assump_26
            case intro assump_38 assump_39 =>
              have assump_86 : (p1 → p1) := by
                intro assump_47
                exact assump_47
              let assump_46 := assump_24 assump_86
              apply False.elim assump_46
      case inr assump_20 =>
        cases assump_18
        case intro assump_55 assump_56 =>
          cases assump_55
          case inl assump_57 =>
            have assump_87 : (p1 → p1) := by
              intro assump_64
              exact assump_64
            let assump_63 := assump_56 assump_87
            apply False.elim assump_63
          case inr assump_58 =>
            cases assump_58
            case intro assump_70 assump_71 =>
              have assump_88 : (p1 → p1) := by
                intro assump_79
                exact assump_79
              let assump_78 := assump_56 assump_88
              apply False.elim assump_78


variable (p5 p3 p2 p0 p4 : Prop)
theorem file93_29327 : (((((p4 ∨ True) ∨ (p2 ∧ False)) → False) → False) ∧ ((((True ∨ True) ∧ (True ∧ p4)) ∧ ((False ∨ p5) ∨ (p0 ∧ p4))) → (((True → p3) → (p2 → False)) → ((p2 → True) → (p5 ∨ p0))))) := by
  apply And.intro
  intro assump_1
  have assump_65 : ((p4 ∨ True) ∨ (p2 ∧ False)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_65
  apply False.elim assump_4
  intro assump_8
  intro assump_9
  intro assump_10
  cases assump_8
  case intro assump_15 assump_16 =>
    cases assump_15
    case intro assump_17 assump_18 =>
      cases assump_17
      case inl assump_19 =>
        cases assump_18
        case intro assump_23 assump_24 =>
          cases assump_16
          case inl assump_29 =>
            cases assump_29
            case inl assump_31 =>
              apply False.elim assump_31
            case inr assump_32 =>
              apply Or.inl
              exact assump_32
          case inr assump_30 =>
            cases assump_30
            case intro assump_37 assump_38 =>
              apply Or.inr
              exact assump_37
      case inr assump_20 =>
        cases assump_18
        case intro assump_45 assump_46 =>
          cases assump_16
          case inl assump_51 =>
            cases assump_51
            case inl assump_53 =>
              apply False.elim assump_53
            case inr assump_54 =>
              apply Or.inl
              exact assump_54
          case inr assump_52 =>
            cases assump_52
            case intro assump_59 assump_60 =>
              apply Or.inr
              exact assump_59


variable (p1 p3 p6 p0 p4 p2 : Prop)
theorem file93_30982 : (((((p6 ∧ False) → False) → False) → False) ∨ ((((p6 → False) → False) → ((p4 ∨ p4) ∧ (p3 → False))) → (((p0 ∧ p2) ∧ (p6 ∨ p0)) → ((p2 → p1) → (p2 → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((p6 ∧ False) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p1 p3 p4 p5 p7 : Prop)
theorem file93_31459 : ((((((p0 → True) → False) → ((p1 ∨ p4) → False)) ∨ (((p3 ∧ p7) ∨ (True → False)) ∨ ((p0 → False) → (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p0 → True) → False) → ((p1 ∨ p4) → False)) ∨ (((p3 ∧ p7) ∨ (True → False)) ∨ ((p0 → False) → (p5 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_31 : (p0 → True) := by
        intro assump_14
        apply True.intro
      let assump_13 := assump_5 assump_31
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_32 : (p0 → True) := by
        intro assump_23
        apply True.intro
      let assump_22 := assump_5 assump_32
      apply False.elim assump_22
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p2 p1 p7 p4 : Prop)
theorem file93_32326 : ((((((True ∨ p2) → False) → False) ∨ (((p1 → False) → False) ∧ ((p7 → p4) → (True → False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ p2) → False) → False) ∨ (((p1 → False) → False) ∧ ((p7 → p4) → (True → False)))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (True ∨ p2) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p6 p2 p3 p4 : Prop)
theorem file93_32886 : ((((((p3 ∨ p4) ∨ (p7 ∧ True)) ∧ ((p2 ∧ False) ∨ (p6 ∧ p7))) → (((False → p2) ∧ (p2 ∨ True)) → ((True → False) → False))) → False) → False) := by
  intro assump_1
  have assump_190 : ((((p3 ∨ p4) ∨ (p7 ∧ True)) ∧ ((p2 ∧ False) ∨ (p6 ∧ p7))) → (((False → p2) ∧ (p2 ∨ True)) → ((True → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_11
      case inl assump_14 =>
        cases assump_5
        case intro assump_18 assump_19 =>
          cases assump_18
          case inl assump_20 =>
            cases assump_20
            case inl assump_22 =>
              cases assump_19
              case inl assump_26 =>
                cases assump_26
                case intro assump_28 assump_29 =>
                  apply False.elim assump_29
              case inr assump_27 =>
                cases assump_27
                case intro assump_34 assump_35 =>
                  have assump_191 : True := by
                    apply True.intro
                  let assump_45 := assump_7 assump_191
                  apply False.elim assump_45
            case inr assump_23 =>
              cases assump_19
              case inl assump_51 =>
                cases assump_51
                case intro assump_53 assump_54 =>
                  apply False.elim assump_54
              case inr assump_52 =>
                cases assump_52
                case intro assump_59 assump_60 =>
                  have assump_192 : True := by
                    apply True.intro
                  let assump_70 := assump_7 assump_192
                  apply False.elim assump_70
          case inr assump_21 =>
            cases assump_21
            case intro assump_74 assump_75 =>
              cases assump_19
              case inl assump_80 =>
                cases assump_80
                case intro assump_82 assump_83 =>
                  apply False.elim assump_83
              case inr assump_81 =>
                cases assump_81
                case intro assump_88 assump_89 =>
                  have assump_193 : True := by
                    apply True.intro
                  let assump_99 := assump_7 assump_193
                  apply False.elim assump_99
      case inr assump_15 =>
        cases assump_5
        case intro assump_105 assump_106 =>
          cases assump_105
          case inl assump_107 =>
            cases assump_107
            case inl assump_109 =>
              cases assump_106
              case inl assump_113 =>
                cases assump_113
                case intro assump_115 assump_116 =>
                  apply False.elim assump_116
              case inr assump_114 =>
                cases assump_114
                case intro assump_121 assump_122 =>
                  have assump_194 : True := by
                    apply True.intro
                  let assump_131 := assump_7 assump_194
                  apply False.elim assump_131
            case inr assump_110 =>
              cases assump_106
              case inl assump_137 =>
                cases assump_137
                case intro assump_139 assump_140 =>
                  apply False.elim assump_140
              case inr assump_138 =>
                cases assump_138
                case intro assump_145 assump_146 =>
                  have assump_195 : True := by
                    apply True.intro
                  let assump_155 := assump_7 assump_195
                  apply False.elim assump_155
          case inr assump_108 =>
            cases assump_108
            case intro assump_159 assump_160 =>
              cases assump_106
              case inl assump_165 =>
                cases assump_165
                case intro assump_167 assump_168 =>
                  apply False.elim assump_168
              case inr assump_166 =>
                cases assump_166
                case intro assump_173 assump_174 =>
                  have assump_196 : True := by
                    apply True.intro
                  let assump_183 := assump_7 assump_196
                  apply False.elim assump_183
  let assump_4 := assump_1 assump_190
  apply False.elim assump_4


variable (p2 p5 p7 p6 p0 p3 : Prop)
theorem file93_37178 : (((((p2 → False) → (p2 → False)) → False) → (((p7 ∨ p7) → (p3 ∨ True)) ∨ ((False → False) ∧ (p7 ∧ p3)))) ∨ ((((p2 → False) ∨ (p6 ∨ True)) ∨ ((False → p0) → False)) → (((p3 → False) → False) ∧ ((p0 ∧ p3) ∧ (p5 ∨ p2))))) := by
  apply Or.inl
  intro assump_13
  apply Or.inl
  intro assump_16
  cases assump_16
  case inl assump_17 =>
    apply Or.inr
    apply True.intro
  case inr assump_18 =>
    apply Or.inr
    apply True.intro


variable (p6 p3 p5 p4 : Prop)
theorem file93_37665 : ((((((p4 ∧ p6) → False) → ((False ∧ False) → False)) → (((p6 → p6) ∨ (False → p4)) ∨ ((p3 → False) ∧ (True ∧ p5)))) → False) → False) := by
  intro assump_9
  have assump_22 : ((((p4 ∧ p6) → False) → ((False ∧ False) → False)) → (((p6 → p6) ∨ (False → p4)) ∨ ((p3 → False) ∧ (True ∧ p5)))) := by
    intro assump_13
    apply Or.inl
    apply Or.inl
    intro assump_16
    exact assump_16
  let assump_12 := assump_9 assump_22
  apply False.elim assump_12


variable (p0 p7 p6 p1 p4 p5 p2 : Prop)
theorem file93_38185 : (((((p6 → p2) ∨ (False ∨ p1)) ∧ ((p4 → True) ∨ (p5 → p7))) ∧ (((p7 ∨ p0) ∨ (p0 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          have assump_84 : ((p7 ∨ p0) ∨ (p0 → False)) := by
            apply Or.inr
            intro assump_17
            have assump_85 : ((p7 ∨ p0) ∨ (p0 → False)) := by
              apply Or.inl
              apply Or.inr
              exact assump_17
            let assump_21 := assump_3 assump_85
            apply False.elim assump_21
          let assump_16 := assump_3 assump_84
          apply False.elim assump_16
        case inr assump_11 =>
          have assump_86 : ((p7 ∨ p0) ∨ (p0 → False)) := by
            apply Or.inr
            intro assump_33
            have assump_87 : ((p7 ∨ p0) ∨ (p0 → False)) := by
              apply Or.inl
              apply Or.inr
              exact assump_33
            let assump_37 := assump_3 assump_87
            apply False.elim assump_37
          let assump_32 := assump_3 assump_86
          apply False.elim assump_32
      case inr assump_7 =>
        cases assump_7
        case inl assump_44 =>
          apply False.elim assump_44
        case inr assump_45 =>
          cases assump_5
          case inl assump_50 =>
            have assump_88 : ((p7 ∨ p0) ∨ (p0 → False)) := by
              apply Or.inr
              intro assump_57
              have assump_89 : ((p7 ∨ p0) ∨ (p0 → False)) := by
                apply Or.inl
                apply Or.inr
                exact assump_57
              let assump_61 := assump_3 assump_89
              apply False.elim assump_61
            let assump_56 := assump_3 assump_88
            apply False.elim assump_56
          case inr assump_51 =>
            have assump_90 : ((p7 ∨ p0) ∨ (p0 → False)) := by
              apply Or.inr
              intro assump_73
              have assump_91 : ((p7 ∨ p0) ∨ (p0 → False)) := by
                apply Or.inl
                apply Or.inr
                exact assump_73
              let assump_77 := assump_3 assump_91
              apply False.elim assump_77
            let assump_72 := assump_3 assump_90
            apply False.elim assump_72


variable (p5 p3 p7 p0 p4 p6 p2 : Prop)
theorem file93_40612 : (((((p5 → False) ∨ (p7 → False)) → ((True → True) ∨ (True → p4))) ∨ (((p7 ∨ p4) ∨ (p2 → False)) → ((p4 ∨ False) ∨ (p3 ∨ p4)))) ∨ ((((p4 ∧ True) ∨ (p6 → p6)) ∧ ((p3 → p5) ∨ (p2 → p6))) → (((p0 ∧ True) ∨ (p3 ∨ p5)) ∧ ((False → False) ∧ (p3 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply True.intro
  case inr assump_3 =>
    apply Or.inl
    intro assump_9
    apply True.intro


variable (p3 p7 p6 p4 p2 : Prop)
theorem file93_41150 : (((((False ∧ False) ∧ (p7 → False)) ∧ ((p3 → p6) → False)) ∧ (((p2 ∧ True) → False) ∨ ((p2 ∧ p6) → (False ∨ True)))) → ((((p4 → False) → False) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          apply False.elim assump_11


variable (p1 p0 p5 p2 p7 p3 p4 p6 : Prop)
theorem file93_41687 : (((((p5 → p2) → (p7 ∧ p7)) → ((p1 → p4) ∨ (p2 → True))) → (((p7 ∨ False) → False) → ((True ∨ p6) ∨ (True ∨ p3)))) ∧ ((((p6 ∨ True) ∨ (True ∧ p6)) ∨ ((p2 ∨ p0) → False)) ∨ (((p5 ∨ p7) ∨ (p2 ∨ p3)) → False))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inl
  apply True.intro
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p4 p5 p2 p0 p1 p6 p3 : Prop)
theorem file93_42143 : (((((p4 → True) ∨ (p2 → p4)) → False) → False) ∨ ((((True ∨ p3) ∧ (p6 → False)) ∨ ((False ∧ p3) → (p0 ∨ p5))) ∧ (((p4 ∧ p6) → (p1 ∨ p5)) ∨ ((p2 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_9 : ((p4 → True) ∨ (p2 → p4)) := by
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p5 p0 p4 p7 p2 p1 p6 : Prop)
theorem file93_42580 : ((((((p1 → p0) → (p4 ∧ p5)) → ((p1 ∨ p7) → (p1 ∨ p1))) → False) ∧ ((((False → False) → (p6 → p6)) ∨ ((p6 → p5) ∨ (p5 ∧ p0))) ∧ (((p7 ∧ p4) ∧ (p0 ∧ p2)) ∧ ((p5 ∨ False) ∧ (True → False))))) → False) := by
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
            case intro assump_16 assump_17 =>
              cases assump_15
              case intro assump_22 assump_23 =>
                cases assump_13
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case inl assump_30 =>
                    have assump_112 : True := by
                      apply True.intro
                    let assump_36 := assump_29 assump_112
                    apply False.elim assump_36
                  case inr assump_31 =>
                    apply False.elim assump_31
      case inr assump_9 =>
        cases assump_9
        case inl assump_42 =>
          cases assump_7
          case intro assump_46 assump_47 =>
            cases assump_46
            case intro assump_48 assump_49 =>
              cases assump_48
              case intro assump_50 assump_51 =>
                cases assump_49
                case intro assump_56 assump_57 =>
                  cases assump_47
                  case intro assump_62 assump_63 =>
                    cases assump_62
                    case inl assump_64 =>
                      have assump_113 : True := by
                        apply True.intro
                      let assump_70 := assump_63 assump_113
                      apply False.elim assump_70
                    case inr assump_65 =>
                      apply False.elim assump_65
        case inr assump_43 =>
          cases assump_43
          case intro assump_76 assump_77 =>
            cases assump_7
            case intro assump_82 assump_83 =>
              cases assump_82
              case intro assump_84 assump_85 =>
                cases assump_84
                case intro assump_86 assump_87 =>
                  cases assump_85
                  case intro assump_92 assump_93 =>
                    cases assump_83
                    case intro assump_98 assump_99 =>
                      cases assump_98
                      case inl assump_100 =>
                        have assump_114 : True := by
                          apply True.intro
                        let assump_106 := assump_99 assump_114
                        apply False.elim assump_106
                      case inr assump_101 =>
                        apply False.elim assump_101


variable (p3 : Prop)
theorem file93_45462 : (((((True → False) → False) ∨ ((False → p3) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : (((True → False) → False) ∨ ((False → p3) → False)) := by
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p2 p5 p1 p6 : Prop)
theorem file93_45916 : ((((((p2 ∨ p2) → False) → ((p1 ∧ p1) ∧ (p5 → p6))) → False) ∧ ((((True ∧ p6) ∨ (False → p2)) ∧ ((p0 ∧ True) → (p0 ∧ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_28 : (((True ∧ p6) ∨ (False → p2)) ∧ ((p0 ∧ True) → (p0 ∧ p0))) := by
      apply And.intro
      apply Or.inr
      intro assump_9
      apply False.elim assump_9
      intro assump_12
      apply And.intro
      cases assump_12
      case intro assump_13 assump_14 =>
        exact assump_13
      cases assump_12
      case intro assump_19 assump_20 =>
        exact assump_19
    let assump_8 := assump_3 assump_28
    apply False.elim assump_8


variable (p7 p5 p1 p2 p6 p3 : Prop)
theorem file93_46656 : (((((p5 ∨ p1) ∧ (False ∧ True)) → ((p7 → False) → (True → False))) ∧ (((p3 ∧ p3) ∧ (False ∨ False)) → ((p1 → False) ∧ (p6 → False)))) ∨ ((((p6 ∨ False) ∧ (True ∨ p1)) → ((p3 ∧ p2) ∧ (p5 ∨ False))) → False)) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
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
  intro assump_24
  apply And.intro
  intro assump_25
  cases assump_24
  case intro assump_28 assump_29 =>
    cases assump_28
    case intro assump_30 assump_31 =>
      cases assump_29
      case inl assump_36 =>
        apply False.elim assump_36
      case inr assump_37 =>
        apply False.elim assump_37
  intro assump_42
  cases assump_24
  case intro assump_45 assump_46 =>
    cases assump_45
    case intro assump_47 assump_48 =>
      cases assump_46
      case inl assump_53 =>
        apply False.elim assump_53
      case inr assump_54 =>
        apply False.elim assump_54


variable (p4 p5 p7 p3 p1 p0 p2 p6 : Prop)
theorem file93_47925 : ((((((p0 → False) ∧ (p2 → p1)) → ((p4 → False) → (p7 → True))) ∧ (((p2 ∨ p3) → (False → p6)) ∧ ((p4 ∨ p7) ∨ (False → p7)))) → ((((p3 ∧ False) → False) ∨ ((p2 ∨ p6) → (p5 → False))) → False)) → False) := by
  intro assump_5
  have assump_30 : ((((p0 → False) ∧ (p2 → p1)) → ((p4 → False) → (p7 → True))) ∧ (((p2 ∨ p3) → (False → p6)) ∧ ((p4 ∨ p7) ∨ (False → p7)))) := by
    apply And.intro
    intro assump_9
    intro assump_10
    intro assump_11
    apply True.intro
    apply And.intro
    intro assump_12
    intro assump_13
    apply False.elim assump_13
    apply Or.inr
    intro assump_16
    apply False.elim assump_16
  let assump_8 := assump_5 assump_30
  have assump_31 : (((p3 ∧ False) → False) ∨ ((p2 ∨ p6) → (p5 → False))) := by
    apply Or.inl
    intro assump_20
    cases assump_20
    case intro assump_21 assump_22 =>
      apply False.elim assump_22
  let assump_19 := assump_8 assump_31
  apply False.elim assump_19


variable (p4 p2 p6 p1 : Prop)
theorem file93_48919 : ((((((False ∨ True) → False) → ((p2 → p6) → (p4 ∨ False))) ∨ (((p1 → p4) → (True ∧ p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False ∨ True) → False) → ((p2 → p6) → (p4 ∨ False))) ∨ (((p1 → p4) → (True ∧ p2)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_19 : (False ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p3 p2 p6 p7 p5 p4 : Prop)
theorem file93_49517 : (((((p5 ∨ p3) ∨ (p5 → p7)) → False) ∧ (((p0 → False) ∨ (p6 → False)) ∧ ((p5 → p6) ∨ (p0 → False)))) → ((((p2 ∨ p2) ∨ (p4 ∨ p4)) → ((p6 → p2) → (p2 → False))) ∨ (((p4 → False) → (p2 → p3)) ∧ ((p0 ∧ p6) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case inl assump_12 =>
          apply Or.inl
          intro assump_16
          intro assump_17
          intro assump_18
          cases assump_16
          case inl assump_23 =>
            cases assump_23
            case inl assump_25 =>
              have assump_470 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_35
                have assump_471 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_35
                let assump_45 := assump_2 assump_471
                apply False.elim assump_45
              let assump_34 := assump_2 assump_470
              apply False.elim assump_34
            case inr assump_26 =>
              have assump_472 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_60
                have assump_473 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_60
                let assump_70 := assump_2 assump_473
                apply False.elim assump_70
              let assump_59 := assump_2 assump_472
              apply False.elim assump_59
          case inr assump_24 =>
            cases assump_24
            case inl assump_77 =>
              have assump_474 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_87
                have assump_475 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_87
                let assump_97 := assump_2 assump_475
                apply False.elim assump_97
              let assump_86 := assump_2 assump_474
              apply False.elim assump_86
            case inr assump_78 =>
              have assump_476 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_112
                have assump_477 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_112
                let assump_122 := assump_2 assump_477
                apply False.elim assump_122
              let assump_111 := assump_2 assump_476
              apply False.elim assump_111
        case inr assump_13 =>
          apply Or.inl
          intro assump_131
          intro assump_132
          intro assump_133
          cases assump_131
          case inl assump_138 =>
            cases assump_138
            case inl assump_140 =>
              have assump_478 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_150
                have assump_479 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_150
                let assump_159 := assump_2 assump_479
                apply False.elim assump_159
              let assump_149 := assump_2 assump_478
              apply False.elim assump_149
            case inr assump_141 =>
              have assump_480 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_174
                have assump_481 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_174
                let assump_183 := assump_2 assump_481
                apply False.elim assump_183
              let assump_173 := assump_2 assump_480
              apply False.elim assump_173
          case inr assump_139 =>
            cases assump_139
            case inl assump_190 =>
              have assump_482 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_200
                have assump_483 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_200
                let assump_209 := assump_2 assump_483
                apply False.elim assump_209
              let assump_199 := assump_2 assump_482
              apply False.elim assump_199
            case inr assump_191 =>
              have assump_484 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_224
                have assump_485 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_224
                let assump_233 := assump_2 assump_485
                apply False.elim assump_233
              let assump_223 := assump_2 assump_484
              apply False.elim assump_223
      case inr assump_9 =>
        cases assump_7
        case inl assump_242 =>
          apply Or.inl
          intro assump_246
          intro assump_247
          intro assump_248
          cases assump_246
          case inl assump_253 =>
            cases assump_253
            case inl assump_255 =>
              have assump_486 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_265
                have assump_487 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_265
                let assump_275 := assump_2 assump_487
                apply False.elim assump_275
              let assump_264 := assump_2 assump_486
              apply False.elim assump_264
            case inr assump_256 =>
              have assump_488 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_290
                have assump_489 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_290
                let assump_300 := assump_2 assump_489
                apply False.elim assump_300
              let assump_289 := assump_2 assump_488
              apply False.elim assump_289
          case inr assump_254 =>
            cases assump_254
            case inl assump_307 =>
              have assump_490 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_317
                have assump_491 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_317
                let assump_327 := assump_2 assump_491
                apply False.elim assump_327
              let assump_316 := assump_2 assump_490
              apply False.elim assump_316
            case inr assump_308 =>
              have assump_492 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_342
                have assump_493 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_342
                let assump_352 := assump_2 assump_493
                apply False.elim assump_352
              let assump_341 := assump_2 assump_492
              apply False.elim assump_341
        case inr assump_243 =>
          apply Or.inl
          intro assump_361
          intro assump_362
          intro assump_363
          cases assump_361
          case inl assump_368 =>
            cases assump_368
            case inl assump_370 =>
              have assump_494 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_380
                have assump_495 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_380
                let assump_389 := assump_2 assump_495
                apply False.elim assump_389
              let assump_379 := assump_2 assump_494
              apply False.elim assump_379
            case inr assump_371 =>
              have assump_496 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_404
                have assump_497 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_404
                let assump_413 := assump_2 assump_497
                apply False.elim assump_413
              let assump_403 := assump_2 assump_496
              apply False.elim assump_403
          case inr assump_369 =>
            cases assump_369
            case inl assump_420 =>
              have assump_498 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_430
                have assump_499 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_430
                let assump_439 := assump_2 assump_499
                apply False.elim assump_439
              let assump_429 := assump_2 assump_498
              apply False.elim assump_429
            case inr assump_421 =>
              have assump_500 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                apply Or.inr
                intro assump_454
                have assump_501 : ((p5 ∨ p3) ∨ (p5 → p7)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_454
                let assump_463 := assump_2 assump_501
                apply False.elim assump_463
              let assump_453 := assump_2 assump_500
              apply False.elim assump_453


variable (p7 p4 p2 p1 p0 p5 p3 : Prop)
theorem file93_59347 : (((((p3 → False) → (p3 → False)) → ((True ∨ p2) ∨ (False ∧ p5))) → False) → ((((True ∨ p4) → False) ∧ ((p0 ∨ p2) ∧ (p3 → False))) → (((True → False) ∨ (False → p5)) → ((p1 → p5) ∧ (p2 ∧ p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    cases assump_2
    case intro assump_11 assump_12 =>
      cases assump_12
      case intro assump_15 assump_16 =>
        cases assump_15
        case inl assump_17 =>
          have assump_215 : (((p3 → False) → (p3 → False)) → ((True ∨ p2) ∨ (False ∧ p5))) := by
            intro assump_26
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_25 := assump_1 assump_215
          apply False.elim assump_25
        case inr assump_18 =>
          have assump_216 : (((p3 → False) → (p3 → False)) → ((True ∨ p2) ∨ (False ∧ p5))) := by
            intro assump_39
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_38 := assump_1 assump_216
          apply False.elim assump_38
  case inr assump_8 =>
    cases assump_2
    case intro assump_47 assump_48 =>
      cases assump_48
      case intro assump_51 assump_52 =>
        cases assump_51
        case inl assump_53 =>
          have assump_217 : (((p3 → False) → (p3 → False)) → ((True ∨ p2) ∨ (False ∧ p5))) := by
            intro assump_62
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_61 := assump_1 assump_217
          apply False.elim assump_61
        case inr assump_54 =>
          have assump_218 : (((p3 → False) → (p3 → False)) → ((True ∨ p2) ∨ (False ∧ p5))) := by
            intro assump_75
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_74 := assump_1 assump_218
          apply False.elim assump_74
  apply And.intro
  cases assump_3
  case inl assump_81 =>
    cases assump_2
    case intro assump_85 assump_86 =>
      cases assump_86
      case intro assump_89 assump_90 =>
        cases assump_89
        case inl assump_91 =>
          have assump_219 : (((p3 → False) → (p3 → False)) → ((True ∨ p2) ∨ (False ∧ p5))) := by
            intro assump_100
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_99 := assump_1 assump_219
          apply False.elim assump_99
        case inr assump_92 =>
          exact assump_92
  case inr assump_82 =>
    cases assump_2
    case intro assump_114 assump_115 =>
      cases assump_115
      case intro assump_118 assump_119 =>
        cases assump_118
        case inl assump_120 =>
          have assump_220 : (((p3 → False) → (p3 → False)) → ((True ∨ p2) ∨ (False ∧ p5))) := by
            intro assump_129
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_128 := assump_1 assump_220
          apply False.elim assump_128
        case inr assump_121 =>
          exact assump_121
  cases assump_3
  case inl assump_141 =>
    cases assump_2
    case intro assump_145 assump_146 =>
      cases assump_146
      case intro assump_149 assump_150 =>
        cases assump_149
        case inl assump_151 =>
          have assump_221 : (((p3 → False) → (p3 → False)) → ((True ∨ p2) ∨ (False ∧ p5))) := by
            intro assump_160
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_159 := assump_1 assump_221
          apply False.elim assump_159
        case inr assump_152 =>
          have assump_222 : (((p3 → False) → (p3 → False)) → ((True ∨ p2) ∨ (False ∧ p5))) := by
            intro assump_173
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_172 := assump_1 assump_222
          apply False.elim assump_172
  case inr assump_142 =>
    cases assump_2
    case intro assump_181 assump_182 =>
      cases assump_182
      case intro assump_185 assump_186 =>
        cases assump_185
        case inl assump_187 =>
          have assump_223 : (((p3 → False) → (p3 → False)) → ((True ∨ p2) ∨ (False ∧ p5))) := by
            intro assump_196
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_195 := assump_1 assump_223
          apply False.elim assump_195
        case inr assump_188 =>
          have assump_224 : (((p3 → False) → (p3 → False)) → ((True ∨ p2) ∨ (False ∧ p5))) := by
            intro assump_209
            apply Or.inl
            apply Or.inl
            apply True.intro
          let assump_208 := assump_1 assump_224
          apply False.elim assump_208


variable (p2 p4 p5 p0 p3 p1 : Prop)
theorem file93_64097 : ((((((True → False) → (False → False)) ∧ ((p1 ∨ p4) → False)) → (((p0 ∨ False) ∧ (p3 ∧ p0)) → ((p5 ∧ p2) ∨ (True ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((True → False) → (False → False)) ∧ ((p1 ∨ p4) → False)) → (((p0 ∨ False) ∧ (p3 ∧ p0)) → ((p5 ∧ p2) ∨ (True ∧ True)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          cases assump_5
          case intro assump_19 assump_20 =>
            apply Or.inr
            apply And.intro
            apply True.intro
            apply True.intro
      case inr assump_10 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p7 p5 p4 p3 p1 p6 p2 p0 : Prop)
theorem file93_64989 : (((((True ∨ p0) → False) ∨ ((False ∧ p5) → (False → False))) ∧ (((False → True) → (True ∨ p6)) → False)) → ((((p5 → p6) ∧ (p6 ∧ False)) ∨ ((p5 ∨ p0) ∧ (p2 ∨ False))) ∨ (((p1 → p2) ∨ (p7 → p5)) → ((p5 ∨ True) ∧ (p4 → p3))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inr
      intro assump_21
      apply And.intro
      cases assump_21
      case inl assump_22 =>
        apply Or.inr
        apply True.intro
      case inr assump_23 =>
        apply Or.inr
        apply True.intro
      intro assump_28
      cases assump_21
      case inl assump_31 =>
        have assump_104 : ((False → True) → (True ∨ p6)) := by
          intro assump_38
          apply Or.inl
          apply True.intro
        let assump_37 := assump_3 assump_104
        apply False.elim assump_37
      case inr assump_32 =>
        have assump_105 : ((False → True) → (True ∨ p6)) := by
          intro assump_49
          apply Or.inl
          apply True.intro
        let assump_48 := assump_3 assump_105
        apply False.elim assump_48
    case inr assump_5 =>
      apply Or.inr
      intro assump_70
      apply And.intro
      cases assump_70
      case inl assump_71 =>
        apply Or.inr
        apply True.intro
      case inr assump_72 =>
        apply Or.inr
        apply True.intro
      intro assump_77
      cases assump_70
      case inl assump_80 =>
        have assump_106 : ((False → True) → (True ∨ p6)) := by
          intro assump_87
          apply Or.inl
          apply True.intro
        let assump_86 := assump_3 assump_106
        apply False.elim assump_86
      case inr assump_81 =>
        have assump_107 : ((False → True) → (True ∨ p6)) := by
          intro assump_98
          apply Or.inl
          apply True.intro
        let assump_97 := assump_3 assump_107
        apply False.elim assump_97


variable (p6 p4 p3 p5 p2 p1 p0 : Prop)
theorem file93_66961 : ((((((p3 ∨ p0) → False) ∨ ((p3 ∧ p4) → (p1 ∨ False))) → False) ∧ ((((p1 → False) ∨ (p6 ∧ p4)) → False) ∧ (((False → False) → False) ∧ ((p2 ∨ p5) → (p4 ∧ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_24 : (False → False) := by
          intro assump_18
          apply False.elim assump_18
        let assump_17 := assump_10 assump_24
        apply False.elim assump_17


variable (p1 p6 p2 p7 p4 p5 p3 : Prop)
theorem file93_67574 : (((((False ∧ p4) ∨ (p5 ∨ False)) ∨ ((p7 → p5) → (p3 ∨ True))) ∨ (((p5 ∨ p1) → False) ∨ ((p3 → p3) → (p6 → False)))) ∨ ((((p7 ∧ p2) → False) → ((p1 ∧ p4) ∧ (False ∨ p4))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply Or.inr
  apply True.intro


variable (p4 p0 p6 p5 p1 p3 : Prop)
theorem file93_67916 : (((((p1 → False) ∨ (True → False)) → ((p0 ∨ p6) ∨ (p3 → p6))) ∧ (((p4 ∧ False) → (p5 ∨ True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((p4 ∧ False) → (p5 ∨ True)) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_11
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p7 p4 p5 : Prop)
theorem file93_68396 : ((((((False ∧ p7) → False) → ((True ∨ True) ∧ (False ∨ True))) ∨ (((False → p7) ∧ (True ∧ p4)) → ((p5 ∨ True) ∨ (p7 ∨ p4)))) → False) → False) := by
  intro assump_9
  have assump_21 : ((((False ∧ p7) → False) → ((True ∨ True) ∧ (False ∨ True))) ∨ (((False → p7) ∧ (True ∧ p4)) → ((p5 ∨ True) ∨ (p7 ∨ p4)))) := by
    apply Or.inl
    intro assump_13
    apply And.intro
    apply Or.inl
    apply True.intro
    apply Or.inr
    apply True.intro
  let assump_12 := assump_9 assump_21
  apply False.elim assump_12


variable (p1 p3 p0 p5 p4 p7 p6 : Prop)
theorem file93_68973 : (((((True → False) → False) ∨ ((p7 → p6) ∧ (p6 ∧ p4))) ∨ (((p6 → p1) → False) ∨ ((p5 → False) ∧ (p3 ∧ p3)))) ∨ ((((p1 → False) ∨ (p7 ∧ p0)) ∨ ((p5 ∧ p7) → (True ∧ p7))) ∧ (((p0 → False) ∨ (p6 ∧ p7)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p0 p3 p1 p7 p6 p4 p5 : Prop)
theorem file93_69431 : (((((p5 → False) → False) ∧ ((p6 → True) → (False ∨ p7))) ∧ (((p6 ∨ False) ∨ (p3 ∨ p7)) → False)) → ((((p2 ∧ p0) → False) ∧ ((p6 → p4) → (p5 → p5))) ∨ (((p6 → p1) → False) ∨ ((True ∧ True) ∧ (True → True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply And.intro
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        have assump_44 : (p6 → True) := by
          intro assump_23
          apply True.intro
        let assump_22 := assump_5 assump_44
        cases assump_22
        case inl assump_25 =>
          apply False.elim assump_25
        case inr assump_26 =>
          have assump_45 : ((p6 ∨ False) ∨ (p3 ∨ p7)) := by
            apply Or.inr
            apply Or.inr
            exact assump_26
          let assump_34 := assump_3 assump_45
          apply False.elim assump_34
      intro assump_38
      intro assump_39
      exact assump_39


variable (p6 p5 p0 p4 p3 : Prop)
theorem file93_70499 : (((((p0 ∨ p3) ∨ (True ∨ p6)) ∨ ((p0 ∨ p0) → (False ∧ False))) → False) → ((((p4 → False) → (True ∧ p0)) ∧ ((p5 → False) ∧ (p5 → False))) → (((p4 ∨ p4) ∧ (p5 → False)) ∧ ((p3 ∧ p6) → (False ∨ p3))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      have assump_57 : (((p0 ∨ p3) ∨ (True ∨ p6)) ∨ ((p0 ∨ p0) → (False ∧ False))) := by
        apply Or.inl
        apply Or.inr
        apply Or.inl
        apply True.intro
      let assump_15 := assump_1 assump_57
      apply False.elim assump_15
  intro assump_19
  cases assump_2
  case intro assump_22 assump_23 =>
    cases assump_23
    case intro assump_26 assump_27 =>
      have assump_58 : (((p0 ∨ p3) ∨ (True ∨ p6)) ∨ ((p0 ∨ p0) → (False ∧ False))) := by
        apply Or.inl
        apply Or.inr
        apply Or.inl
        apply True.intro
      let assump_34 := assump_1 assump_58
      apply False.elim assump_34
  intro assump_38
  cases assump_38
  case intro assump_39 assump_40 =>
    cases assump_2
    case intro assump_45 assump_46 =>
      cases assump_46
      case intro assump_49 assump_50 =>
        apply Or.inr
        exact assump_39


variable (p2 p6 p7 p0 p3 p4 p1 : Prop)
theorem file93_71812 : (((((p2 ∨ p6) → (p3 ∧ False)) ∧ ((p4 ∧ p6) ∧ (p7 ∧ True))) ∧ (((p0 ∨ p0) ∧ (p0 → True)) → ((p4 ∧ False) ∨ (True ∨ p6)))) → ((((p6 ∧ False) ∨ (p2 → p7)) ∨ ((True ∧ p1) → (p2 → True))) ∨ (((p4 ∧ p7) ∨ (p1 → p0)) ∧ ((p6 ∨ p4) → (True → False))))) := by
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
            apply Or.inl
            apply Or.inl
            apply Or.inr
            intro assump_24
            exact assump_16


variable (p1 p0 p2 p5 p3 p7 p4 p6 : Prop)
theorem file93_72575 : ((((((p0 ∧ p2) ∧ (p2 → p3)) ∨ ((p2 ∨ p1) → False)) ∧ (((p7 → False) ∧ (True ∧ p6)) ∧ ((True ∨ True) ∨ (p0 ∨ p7)))) ∧ ((((p4 ∨ p5) → False) → ((p6 ∨ p3) ∨ (p4 → p7))) → False)) → False) := by
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
            cases assump_5
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_21
                case intro assump_24 assump_25 =>
                  cases assump_19
                  case inl assump_30 =>
                    cases assump_30
                    case inl assump_32 =>
                      have assump_144 : (((p4 ∨ p5) → False) → ((p6 ∨ p3) ∨ (p4 → p7))) := by
                        intro assump_39
                        apply Or.inl
                        apply Or.inl
                        exact assump_25
                      let assump_38 := assump_3 assump_144
                      apply False.elim assump_38
                    case inr assump_33 =>
                      have assump_145 : (((p4 ∨ p5) → False) → ((p6 ∨ p3) ∨ (p4 → p7))) := by
                        intro assump_50
                        apply Or.inl
                        apply Or.inl
                        exact assump_25
                      let assump_49 := assump_3 assump_145
                      apply False.elim assump_49
                  case inr assump_31 =>
                    cases assump_31
                    case inl assump_56 =>
                      have assump_146 : (((p4 ∨ p5) → False) → ((p6 ∨ p3) ∨ (p4 → p7))) := by
                        intro assump_63
                        apply Or.inl
                        apply Or.inl
                        exact assump_25
                      let assump_62 := assump_3 assump_146
                      apply False.elim assump_62
                    case inr assump_57 =>
                      have assump_147 : (((p4 ∨ p5) → False) → ((p6 ∨ p3) ∨ (p4 → p7))) := by
                        intro assump_74
                        apply Or.inl
                        apply Or.inl
                        exact assump_25
                      let assump_73 := assump_3 assump_147
                      apply False.elim assump_73
      case inr assump_7 =>
        cases assump_5
        case intro assump_82 assump_83 =>
          cases assump_82
          case intro assump_84 assump_85 =>
            cases assump_85
            case intro assump_88 assump_89 =>
              cases assump_83
              case inl assump_94 =>
                cases assump_94
                case inl assump_96 =>
                  have assump_148 : (((p4 ∨ p5) → False) → ((p6 ∨ p3) ∨ (p4 → p7))) := by
                    intro assump_103
                    apply Or.inl
                    apply Or.inl
                    exact assump_89
                  let assump_102 := assump_3 assump_148
                  apply False.elim assump_102
                case inr assump_97 =>
                  have assump_149 : (((p4 ∨ p5) → False) → ((p6 ∨ p3) ∨ (p4 → p7))) := by
                    intro assump_114
                    apply Or.inl
                    apply Or.inl
                    exact assump_89
                  let assump_113 := assump_3 assump_149
                  apply False.elim assump_113
              case inr assump_95 =>
                cases assump_95
                case inl assump_120 =>
                  have assump_150 : (((p4 ∨ p5) → False) → ((p6 ∨ p3) ∨ (p4 → p7))) := by
                    intro assump_127
                    apply Or.inl
                    apply Or.inl
                    exact assump_89
                  let assump_126 := assump_3 assump_150
                  apply False.elim assump_126
                case inr assump_121 =>
                  have assump_151 : (((p4 ∨ p5) → False) → ((p6 ∨ p3) ∨ (p4 → p7))) := by
                    intro assump_138
                    apply Or.inl
                    apply Or.inl
                    exact assump_89
                  let assump_137 := assump_3 assump_151
                  apply False.elim assump_137


variable (p3 p0 p2 p4 p1 p7 p6 p5 : Prop)
theorem file93_77026 : (((((p4 → p6) → (p1 → p0)) → False) → (((p4 ∧ p1) → (p3 → p3)) ∧ ((p4 ∧ p7) → (p5 → p4)))) ∨ ((((p0 → p4) ∨ (p2 ∧ p5)) ∨ ((p7 → False) → False)) → (((True → p0) ∧ (p6 → False)) ∧ ((p7 → False) → (True → True))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    exact assump_3
  intro assump_14
  intro assump_15
  cases assump_14
  case intro assump_18 assump_19 =>
    exact assump_18


variable (p4 p3 p0 p1 p2 p6 p5 : Prop)
theorem file93_77572 : (((((p6 → False) → (p5 → False)) ∨ ((True → p4) ∨ (p4 ∧ p0))) ∧ (((p4 ∨ p0) → False) ∧ ((False ∧ False) ∧ (p3 → False)))) → ((((p2 → p4) ∧ (p0 ∨ p5)) ∧ ((p4 → False) ∨ (False → True))) → (((False ∨ False) ∧ (True → True)) → ((p1 → p4) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      apply False.elim assump_9
    case inr assump_10 =>
      apply False.elim assump_10


variable (p1 p3 p4 p0 : Prop)
theorem file93_78133 : (((((False ∨ True) → False) ∧ ((p0 ∨ p0) ∧ (p3 ∧ p0))) ∧ (((p4 ∨ p0) → False) ∧ ((p0 → p0) ∨ (p1 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_9
          case intro assump_14 assump_15 =>
            cases assump_3
            case intro assump_20 assump_21 =>
              cases assump_21
              case inl assump_24 =>
                have assump_70 : (p4 ∨ p0) := by
                  apply Or.inr
                  exact assump_15
                let assump_30 := assump_20 assump_70
                apply False.elim assump_30
              case inr assump_25 =>
                have assump_71 : (p4 ∨ p0) := by
                  apply Or.inr
                  exact assump_15
                let assump_37 := assump_20 assump_71
                apply False.elim assump_37
        case inr assump_11 =>
          cases assump_9
          case intro assump_43 assump_44 =>
            cases assump_3
            case intro assump_49 assump_50 =>
              cases assump_50
              case inl assump_53 =>
                have assump_72 : (p4 ∨ p0) := by
                  apply Or.inr
                  exact assump_44
                let assump_59 := assump_49 assump_72
                apply False.elim assump_59
              case inr assump_54 =>
                have assump_73 : (p4 ∨ p0) := by
                  apply Or.inr
                  exact assump_44
                let assump_66 := assump_49 assump_73
                apply False.elim assump_66


variable (p7 p1 p2 p6 p0 p4 : Prop)
theorem file93_79910 : (((((True → False) ∧ (p4 ∨ p6)) ∧ ((p1 ∧ False) ∧ (False → False))) → (((p7 ∧ p0) ∧ (p4 → False)) ∨ ((p7 ∧ p4) ∨ (p0 → p2)))) ∨ ((((p0 ∨ p6) → False) ∧ ((p6 → p7) → False)) ∨ (((p0 → p1) ∧ (p2 ∨ True)) → False))) := by
  apply Or.inl
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case inl assump_12 =>
        cases assump_7
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            apply False.elim assump_19
      case inr assump_13 =>
        cases assump_7
        case intro assump_26 assump_27 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            apply False.elim assump_29


variable (p7 p0 p5 p2 p3 p4 p1 : Prop)
theorem file93_80755 : ((((((False → p4) ∧ (p5 ∨ p0)) → ((p1 → p0) → (p5 → False))) ∧ (((p4 → False) → False) ∨ ((p2 ∨ p5) → (p0 → False)))) ∧ ((((p0 ∧ False) ∧ (p2 ∨ p4)) ∨ ((p7 ∧ False) → (p7 ∧ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_52 : (((p0 ∧ False) ∧ (p2 ∨ p4)) ∨ ((p7 ∧ False) → (p7 ∧ p3))) := by
          apply Or.inr
          intro assump_15
          apply And.intro
          cases assump_15
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
          cases assump_15
          case intro assump_22 assump_23 =>
            apply False.elim assump_23
        let assump_14 := assump_3 assump_52
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_53 : (((p0 ∧ False) ∧ (p2 ∨ p4)) ∨ ((p7 ∧ False) → (p7 ∧ p3))) := by
          apply Or.inr
          intro assump_36
          apply And.intro
          cases assump_36
          case intro assump_37 assump_38 =>
            apply False.elim assump_38
          cases assump_36
          case intro assump_43 assump_44 =>
            apply False.elim assump_44
        let assump_35 := assump_3 assump_53
        apply False.elim assump_35


variable (p0 p3 p5 p7 p2 p1 : Prop)
theorem file93_82139 : (((((p3 ∧ False) ∨ (p3 ∧ p3)) ∧ ((p3 ∧ p0) → (False ∧ p3))) → False) → ((((p1 → False) ∨ (p3 → False)) → False) → (((True ∨ p1) ∨ (p5 ∨ p2)) ∨ ((p1 ∧ p0) → (p3 ∨ p7))))) := by
  intro assump_5
  intro assump_6
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p1 p3 p0 p7 : Prop)
theorem file93_82467 : (((((False → True) → False) → ((p3 → True) ∨ (p3 → False))) → False) → ((((False ∨ p1) → False) → False) ∨ (((p7 ∨ p0) ∧ (p0 → False)) ∧ ((p3 ∨ False) ∨ (p7 ∨ p0))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_16 : (((False → True) → False) → ((p3 → True) ∨ (p3 → False))) := by
    intro assump_9
    apply Or.inl
    intro assump_12
    apply True.intro
  let assump_8 := assump_1 assump_16
  apply False.elim assump_8


variable (p3 p5 p0 p1 : Prop)
theorem file93_82968 : ((((((p0 → False) ∨ (p3 → False)) → ((p3 ∧ False) ∨ (p1 ∨ p5))) → False) ∧ ((((False → False) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((False → False) → False) → False) := by
      intro assump_9
      have assump_23 : (False → False) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_9 assump_23
      apply False.elim assump_12
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p3 p6 p5 p1 p4 p7 p2 p0 : Prop)
theorem file93_83571 : (((((p1 → True) ∧ (False ∧ p7)) → ((True ∨ p4) ∨ (p3 → False))) ∨ (((p2 ∨ p1) ∨ (p5 ∨ p3)) ∨ ((True → False) → False))) ∨ ((((p5 → False) ∧ (True ∧ p4)) ∧ ((p1 ∧ p3) → (True ∨ False))) → (((p5 ∧ False) ∨ (p0 → False)) ∧ ((p3 → False) ∨ (p6 ∨ p2))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_6


variable (p7 p6 p2 p0 p3 : Prop)
theorem file93_84069 : ((((((True → False) ∨ (p7 ∨ p0)) → False) → False) ∧ ((((p2 → False) → False) ∧ ((p3 → False) ∧ (True → False))) ∧ (((True ∨ False) → False) ∨ ((p6 ∨ p3) ∨ (p7 ∧ True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_7
          case inl assump_18 =>
            have assump_55 : (True ∨ False) := by
              apply Or.inl
              apply True.intro
            let assump_22 := assump_18 assump_55
            apply False.elim assump_22
          case inr assump_19 =>
            cases assump_19
            case inl assump_26 =>
              cases assump_26
              case inl assump_28 =>
                have assump_56 : True := by
                  apply True.intro
                let assump_33 := assump_13 assump_56
                apply False.elim assump_33
              case inr assump_29 =>
                have assump_57 : True := by
                  apply True.intro
                let assump_40 := assump_13 assump_57
                apply False.elim assump_40
            case inr assump_27 =>
              cases assump_27
              case intro assump_44 assump_45 =>
                have assump_58 : True := by
                  apply True.intro
                let assump_51 := assump_13 assump_58
                apply False.elim assump_51


variable (p2 p5 p3 p7 p6 p1 : Prop)
theorem file93_85649 : (((((p2 ∧ p1) → (p1 ∧ False)) → ((False → False) → (False → p2))) → False) → ((((p6 → p5) ∧ (p3 ∨ p5)) → ((False → True) ∨ (p5 → p7))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_16 : (((p2 ∧ p1) → (p1 ∧ False)) → ((False → False) → (False → p2))) := by
    intro assump_8
    intro assump_9
    intro assump_10
    apply False.elim assump_10
  let assump_7 := assump_1 assump_16
  apply False.elim assump_7


variable (p7 p3 p4 p6 p0 : Prop)
theorem file93_86134 : ((((((p4 ∨ p7) ∧ (False ∧ p0)) → ((p0 ∧ p4) → (p4 ∨ False))) → (((p6 ∧ False) → (False ∨ False)) ∨ ((p4 ∨ p3) ∧ (True ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p4 ∨ p7) ∧ (False ∧ p0)) → ((p0 ∧ p4) → (p4 ∨ False))) → (((p6 ∧ False) → (False ∨ False)) ∨ ((p4 ∨ p3) ∧ (True ∨ p3)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p7 p6 p0 p3 p1 : Prop)
theorem file93_86721 : ((((((p3 → False) → False) ∧ ((p6 ∨ p7) → (p1 ∨ False))) → (((p0 → p3) ∧ (p6 ∨ p1)) → ((p0 ∧ p1) → (p1 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_39 : ((((p3 → False) → False) ∧ ((p6 ∨ p7) → (p1 ∨ False))) → (((p0 → p3) ∧ (p6 ∨ p1)) → ((p0 ∧ p1) → (p1 ∨ p4)))) := by
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
            apply Or.inl
            exact assump_9
        case inr assump_19 =>
          cases assump_5
          case intro assump_30 assump_31 =>
            apply Or.inl
            exact assump_19
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p5 p2 p7 p3 : Prop)
theorem file93_87628 : (((((p2 ∧ p5) → False) → False) ∧ (((False → p7) → (p2 → False)) ∧ ((p5 ∨ p7) ∧ (p3 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          have assump_82 : ((p2 ∧ p5) → False) := by
            intro assump_26
            cases assump_26
            case intro assump_27 assump_28 =>
              have assump_83 : (False → p7) := by
                intro assump_38
                apply False.elim assump_38
              let assump_37 := assump_6 assump_83
              have assump_84 : p2 := by
                exact assump_27
              let assump_41 := assump_37 assump_84
              apply False.elim assump_41
          let assump_25 := assump_2 assump_82
          apply False.elim assump_25
        case inr assump_13 =>
          have assump_85 : ((p2 ∧ p5) → False) := by
            intro assump_60
            cases assump_60
            case intro assump_61 assump_62 =>
              have assump_86 : (False → p7) := by
                intro assump_72
                apply False.elim assump_72
              let assump_71 := assump_6 assump_86
              have assump_87 : p2 := by
                exact assump_61
              let assump_75 := assump_71 assump_87
              apply False.elim assump_75
          let assump_59 := assump_2 assump_85
          apply False.elim assump_59


variable (p7 p1 : Prop)
theorem file93_89209 : (((((True ∨ p1) → (False → False)) → ((p7 ∧ p1) → (p1 → True))) → False) → False) := by
  intro assump_1
  have assump_11 : (((True ∨ p1) → (False → False)) → ((p7 ∧ p1) → (p1 → True))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p0 p7 p1 p6 p2 : Prop)
theorem file93_89604 : (((((p1 ∨ False) → False) → ((True → False) → (p1 → False))) → False) → ((((False → False) ∧ (False ∨ True)) ∨ ((p2 ∨ p7) → (p4 ∧ p2))) → (((p0 ∧ p0) → (False ∨ p6)) → False))) := by
  intro assump_7
  intro assump_8
  intro assump_9
  cases assump_8
  case inl assump_12 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      cases assump_15
      case inl assump_18 =>
        apply False.elim assump_18
      case inr assump_19 =>
        have assump_64 : (((p1 ∨ False) → False) → ((True → False) → (p1 → False))) := by
          intro assump_27
          intro assump_28
          intro assump_29
          have assump_65 : (p1 ∨ False) := by
            apply Or.inl
            exact assump_29
          let assump_36 := assump_27 assump_65
          apply False.elim assump_36
        let assump_26 := assump_7 assump_64
        apply False.elim assump_26
  case inr assump_13 =>
    have assump_66 : (((p1 ∨ False) → False) → ((True → False) → (p1 → False))) := by
      intro assump_48
      intro assump_49
      intro assump_50
      have assump_67 : (p1 ∨ False) := by
        apply Or.inl
        exact assump_50
      let assump_57 := assump_48 assump_67
      apply False.elim assump_57
    let assump_47 := assump_7 assump_66
    apply False.elim assump_47


variable (p5 p7 p1 p2 p0 : Prop)
theorem file93_90947 : ((((((False ∨ p7) ∨ (p2 → False)) → False) → (((p5 ∧ p0) ∧ (p1 ∧ p2)) → ((False ∨ p7) → False))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((False ∨ p7) ∨ (p2 → False)) → False) → (((p5 ∧ p0) ∧ (p1 ∧ p2)) → ((False ∨ p7) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case inl assump_8 =>
      apply False.elim assump_8
    case inr assump_9 =>
      cases assump_6
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_15
          case intro assump_22 assump_23 =>
            have assump_38 : ((False ∨ p7) ∨ (p2 → False)) := by
              apply Or.inl
              apply Or.inr
              exact assump_9
            let assump_30 := assump_5 assump_38
            apply False.elim assump_30
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p2 p6 p7 p3 p5 p4 p0 : Prop)
theorem file93_91923 : (((((p6 → False) ∧ (p0 → p5)) → ((p7 ∧ p3) → (p2 ∧ p0))) ∧ (((True ∨ p4) ∧ (p7 → p6)) ∧ ((False ∨ True) → False))) → ((((p4 → False) ∧ (True → False)) ∧ ((p2 ∧ p3) → False)) ∨ (((p6 ∨ p3) → False) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          apply Or.inl
          apply And.intro
          apply And.intro
          intro assump_18
          have assump_80 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_22 := assump_7 assump_80
          apply False.elim assump_22
          intro assump_26
          have assump_81 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_29 := assump_7 assump_81
          apply False.elim assump_29
          intro assump_33
          cases assump_33
          case intro assump_34 assump_35 =>
            have assump_82 : (False ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_42 := assump_7 assump_82
            apply False.elim assump_42
        case inr assump_11 =>
          apply Or.inl
          apply And.intro
          apply And.intro
          intro assump_52
          have assump_83 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_56 := assump_7 assump_83
          apply False.elim assump_56
          intro assump_60
          have assump_84 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_63 := assump_7 assump_84
          apply False.elim assump_63
          intro assump_67
          cases assump_67
          case intro assump_68 assump_69 =>
            have assump_85 : (False ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_76 := assump_7 assump_85
            apply False.elim assump_76


variable (p4 p0 : Prop)
theorem file93_94026 : ((((((False ∧ p4) ∨ (p0 → p0)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False ∧ p4) ∨ (p0 → p0)) → False) → False) := by
    intro assump_5
    have assump_19 : ((False ∧ p4) ∨ (p0 → p0)) := by
      apply Or.inr
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p7 p1 p2 p0 p4 p6 p5 : Prop)
theorem file93_94522 : (((((p5 ∧ True) ∨ (p0 → p5)) ∧ ((False ∧ p1) ∨ (p4 → p7))) → (((p7 → p4) ∧ (p5 → False)) → ((p6 → False) → (p2 ∨ p0)))) → ((((p4 ∧ p0) ∨ (p1 → p2)) ∧ ((p3 ∨ p0) ∧ (p7 ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_4
        case intro assump_13 assump_14 =>
          cases assump_13
          case inl assump_15 =>
            cases assump_14
            case intro assump_19 assump_20 =>
              apply False.elim assump_20
          case inr assump_16 =>
            cases assump_14
            case intro assump_27 assump_28 =>
              apply False.elim assump_28
    case inr assump_6 =>
      cases assump_4
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


variable (p7 p0 p3 p1 p6 p5 p4 : Prop)
theorem file93_95740 : (((((p0 → False) → False) ∨ ((p4 ∨ p6) → (p3 → p6))) ∧ (((True → False) ∨ (p4 → False)) ∧ ((p6 → False) ∧ (p4 ∧ p7)))) → ((((p3 → False) ∧ (p7 → p3)) → ((p1 ∨ p5) → False)) → (((p4 → False) → False) ∨ ((p0 → False) ∨ (p0 ∧ False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case intro assump_17 assump_18 =>
            cases assump_18
            case intro assump_21 assump_22 =>
              apply Or.inl
              intro assump_27
              have assump_97 : p4 := by
                exact assump_21
              let assump_30 := assump_27 assump_97
              apply False.elim assump_30
        case inr assump_14 =>
          cases assump_12
          case intro assump_36 assump_37 =>
            cases assump_37
            case intro assump_40 assump_41 =>
              apply Or.inl
              intro assump_46
              have assump_98 : p4 := by
                exact assump_40
              let assump_49 := assump_46 assump_98
              apply False.elim assump_49
    case inr assump_8 =>
      cases assump_6
      case intro assump_55 assump_56 =>
        cases assump_55
        case inl assump_57 =>
          cases assump_56
          case intro assump_61 assump_62 =>
            cases assump_62
            case intro assump_65 assump_66 =>
              apply Or.inl
              intro assump_71
              have assump_99 : p4 := by
                exact assump_65
              let assump_74 := assump_71 assump_99
              apply False.elim assump_74
        case inr assump_58 =>
          cases assump_56
          case intro assump_80 assump_81 =>
            cases assump_81
            case intro assump_84 assump_85 =>
              apply Or.inl
              intro assump_90
              have assump_100 : p4 := by
                exact assump_84
              let assump_93 := assump_90 assump_100
              apply False.elim assump_93


variable (p7 p4 p3 p1 p6 p5 : Prop)
theorem file93_97946 : ((((((p3 ∧ p6) → False) → False) → (((p4 → True) ∨ (True → p7)) ∨ ((p4 ∨ p1) ∨ (p7 → False)))) → ((((False → False) → False) → ((False ∨ p5) ∨ (p1 → False))) → False)) → False) := by
  intro assump_29
  have assump_55 : ((((p3 ∧ p6) → False) → False) → (((p4 → True) ∨ (True → p7)) ∨ ((p4 ∨ p1) ∨ (p7 → False)))) := by
    intro assump_33
    apply Or.inl
    apply Or.inl
    intro assump_36
    apply True.intro
  let assump_32 := assump_29 assump_55
  have assump_56 : (((False → False) → False) → ((False ∨ p5) ∨ (p1 → False))) := by
    intro assump_38
    apply Or.inr
    intro assump_41
    have assump_57 : (False → False) := by
      intro assump_46
      apply False.elim assump_46
    let assump_45 := assump_38 assump_57
    apply False.elim assump_45
  let assump_37 := assump_32 assump_56
  apply False.elim assump_37


variable (p3 p4 p1 p2 p0 p6 p5 p7 : Prop)
theorem file93_98845 : ((((((p7 → p3) ∧ (False ∨ p0)) ∨ ((p1 → p5) ∧ (p4 → False))) → (((False ∨ p6) ∧ (p5 ∧ p7)) → ((p4 → p2) → (p5 ∨ p0)))) → False) → False) := by
  intro assump_5
  have assump_49 : ((((p7 → p3) ∧ (False ∨ p0)) ∨ ((p1 → p5) ∧ (p4 → False))) → (((False ∨ p6) ∧ (p5 ∧ p7)) → ((p4 → p2) → (p5 ∨ p0)))) := by
    intro assump_9
    intro assump_10
    intro assump_11
    cases assump_10
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        apply False.elim assump_16
      case inr assump_17 =>
        cases assump_15
        case intro assump_22 assump_23 =>
          cases assump_9
          case inl assump_28 =>
            cases assump_28
            case intro assump_30 assump_31 =>
              cases assump_31
              case inl assump_34 =>
                apply False.elim assump_34
              case inr assump_35 =>
                apply Or.inl
                exact assump_22
          case inr assump_29 =>
            cases assump_29
            case intro assump_40 assump_41 =>
              apply Or.inl
              exact assump_22
  let assump_8 := assump_5 assump_49
  apply False.elim assump_8


variable (p0 p5 p7 p2 p1 p3 p6 : Prop)
theorem file93_100071 : (((((p1 ∧ p7) → False) ∨ ((p6 ∧ p3) → (p2 → False))) ∧ (((True ∧ False) → (p0 → False)) → False)) → ((((p7 → False) → (p0 ∧ p6)) ∨ ((p2 ∨ p7) ∧ (p0 ∨ p3))) ∨ (((p0 → False) → (p2 ∧ p0)) ∨ ((p0 → p0) → (p5 ∨ p6))))) := by
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inl
      apply Or.inl
      intro assump_13
      apply And.intro
      have assump_87 : ((True ∧ False) → (p0 → False)) := by
        intro assump_18
        intro assump_19
        cases assump_18
        case intro assump_22 assump_23 =>
          apply False.elim assump_23
      let assump_17 := assump_6 assump_87
      apply False.elim assump_17
      have assump_88 : ((True ∧ False) → (p0 → False)) := by
        intro assump_35
        intro assump_36
        cases assump_35
        case intro assump_39 assump_40 =>
          apply False.elim assump_40
      let assump_34 := assump_6 assump_88
      apply False.elim assump_34
    case inr assump_8 =>
      apply Or.inl
      apply Or.inl
      intro assump_52
      apply And.intro
      have assump_89 : ((True ∧ False) → (p0 → False)) := by
        intro assump_57
        intro assump_58
        cases assump_57
        case intro assump_61 assump_62 =>
          apply False.elim assump_62
      let assump_56 := assump_6 assump_89
      apply False.elim assump_56
      have assump_90 : ((True ∧ False) → (p0 → False)) := by
        intro assump_74
        intro assump_75
        cases assump_74
        case intro assump_78 assump_79 =>
          apply False.elim assump_79
      let assump_73 := assump_6 assump_90
      apply False.elim assump_73


variable (p5 p2 p3 p6 p0 p4 : Prop)
theorem file93_101801 : (((((p0 → False) ∧ (p6 ∧ True)) ∨ ((p4 ∨ p2) ∨ (p3 → p5))) ∧ (((p6 ∨ True) → False) ∧ ((True ∧ p0) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            have assump_70 : (p6 ∨ True) := by
              apply Or.inl
              exact assump_10
            let assump_23 := assump_16 assump_70
            apply False.elim assump_23
    case inr assump_5 =>
      cases assump_5
      case inl assump_27 =>
        cases assump_27
        case inl assump_29 =>
          cases assump_3
          case intro assump_33 assump_34 =>
            have assump_71 : (p6 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_40 := assump_33 assump_71
            apply False.elim assump_40
        case inr assump_30 =>
          cases assump_3
          case intro assump_46 assump_47 =>
            have assump_72 : (p6 ∨ True) := by
              apply Or.inr
              apply True.intro
            let assump_53 := assump_46 assump_72
            apply False.elim assump_53
      case inr assump_28 =>
        cases assump_3
        case intro assump_59 assump_60 =>
          have assump_73 : (p6 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_66 := assump_59 assump_73
          apply False.elim assump_66


variable (p7 p5 p0 p6 p1 p4 : Prop)
theorem file93_103441 : (((((p5 → False) → (p6 → p6)) ∧ ((False → False) ∨ (p0 → False))) ∨ (((p4 → False) ∨ (p1 ∨ p6)) ∧ ((p0 ∧ p1) ∨ (p6 → False)))) ∨ ((((p7 → p7) → (p0 ∧ p0)) → False) ∧ (((p4 ∨ p4) → (p1 → p0)) → ((p4 ∧ True) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  exact assump_2
  apply Or.inl
  intro assump_7
  apply False.elim assump_7


variable (p2 p3 p7 p5 p0 p1 p6 : Prop)
theorem file93_103887 : ((((((p2 ∨ p5) → (False ∨ True)) ∨ ((True ∧ p7) ∨ (p3 → False))) ∨ (((p6 → p0) ∨ (p6 → p7)) → ((p2 ∧ p7) ∨ (p1 ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p2 ∨ p5) → (False ∨ True)) ∨ ((True ∧ p7) ∨ (p3 → False))) ∨ (((p6 → p0) ∨ (p6 → p7)) → ((p2 ∧ p7) ∨ (p1 ∨ p5)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inr
      apply True.intro
    case inr assump_7 =>
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p2 p1 p0 p5 p4 p6 p3 p7 : Prop)
theorem file93_104528 : (((((p6 → False) ∨ (p0 ∧ True)) ∧ ((p2 → False) → False)) ∧ (((False ∧ p3) ∨ (p4 ∧ p4)) ∨ ((p3 ∧ p1) ∧ (p5 → p1)))) → ((((p5 → False) → False) ∨ ((p7 ∨ p7) → (False ∧ False))) → (((False → p6) → (p1 ∨ p4)) ∨ ((p1 ∧ p4) ∨ (p4 ∨ p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case inl assump_11 =>
          cases assump_8
          case inl assump_17 =>
            cases assump_17
            case inl assump_19 =>
              cases assump_19
              case intro assump_21 assump_22 =>
                apply False.elim assump_21
            case inr assump_20 =>
              cases assump_20
              case intro assump_25 assump_26 =>
                apply Or.inl
                intro assump_31
                apply Or.inr
                exact assump_26
          case inr assump_18 =>
            cases assump_18
            case intro assump_34 assump_35 =>
              cases assump_34
              case intro assump_36 assump_37 =>
                apply Or.inl
                intro assump_44
                apply Or.inl
                exact assump_37
        case inr assump_12 =>
          cases assump_12
          case intro assump_47 assump_48 =>
            cases assump_8
            case inl assump_55 =>
              cases assump_55
              case inl assump_57 =>
                cases assump_57
                case intro assump_59 assump_60 =>
                  apply False.elim assump_59
              case inr assump_58 =>
                cases assump_58
                case intro assump_63 assump_64 =>
                  apply Or.inl
                  intro assump_69
                  apply Or.inr
                  exact assump_64
            case inr assump_56 =>
              cases assump_56
              case intro assump_72 assump_73 =>
                cases assump_72
                case intro assump_74 assump_75 =>
                  apply Or.inl
                  intro assump_82
                  apply Or.inl
                  exact assump_75
  case inr assump_4 =>
    cases assump_1
    case intro assump_87 assump_88 =>
      cases assump_87
      case intro assump_89 assump_90 =>
        cases assump_89
        case inl assump_91 =>
          cases assump_88
          case inl assump_97 =>
            cases assump_97
            case inl assump_99 =>
              cases assump_99
              case intro assump_101 assump_102 =>
                apply False.elim assump_101
            case inr assump_100 =>
              cases assump_100
              case intro assump_105 assump_106 =>
                apply Or.inl
                intro assump_111
                apply Or.inr
                exact assump_106
          case inr assump_98 =>
            cases assump_98
            case intro assump_114 assump_115 =>
              cases assump_114
              case intro assump_116 assump_117 =>
                apply Or.inl
                intro assump_124
                apply Or.inl
                exact assump_117
        case inr assump_92 =>
          cases assump_92
          case intro assump_127 assump_128 =>
            cases assump_88
            case inl assump_135 =>
              cases assump_135
              case inl assump_137 =>
                cases assump_137
                case intro assump_139 assump_140 =>
                  apply False.elim assump_139
              case inr assump_138 =>
                cases assump_138
                case intro assump_143 assump_144 =>
                  apply Or.inl
                  intro assump_149
                  apply Or.inr
                  exact assump_144
            case inr assump_136 =>
              cases assump_136
              case intro assump_152 assump_153 =>
                cases assump_152
                case intro assump_154 assump_155 =>
                  apply Or.inl
                  intro assump_162
                  apply Or.inl
                  exact assump_155


variable (p5 p4 p7 p1 p6 : Prop)
theorem file93_108718 : ((((((p6 ∨ False) → (p1 → False)) → False) ∨ (((p6 → False) ∨ (True ∧ p7)) ∨ ((False ∨ p6) → False))) ∧ ((((p5 ∧ p6) ∨ (True ∨ True)) ∨ ((p4 → p6) ∨ (p6 ∨ p7))) → False)) → False) := by
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      have assump_51 : (((p5 ∧ p6) ∨ (True ∨ True)) ∨ ((p4 → p6) ∨ (p6 ∨ p7))) := by
        apply Or.inl
        apply Or.inr
        apply Or.inl
        apply True.intro
      let assump_15 := assump_8 assump_51
      apply False.elim assump_15
    case inr assump_10 =>
      cases assump_10
      case inl assump_19 =>
        cases assump_19
        case inl assump_21 =>
          have assump_52 : (((p5 ∧ p6) ∨ (True ∨ True)) ∨ ((p4 → p6) ∨ (p6 ∨ p7))) := by
            apply Or.inl
            apply Or.inr
            apply Or.inl
            apply True.intro
          let assump_27 := assump_8 assump_52
          apply False.elim assump_27
        case inr assump_22 =>
          cases assump_22
          case intro assump_31 assump_32 =>
            have assump_53 : (((p5 ∧ p6) ∨ (True ∨ True)) ∨ ((p4 → p6) ∨ (p6 ∨ p7))) := by
              apply Or.inl
              apply Or.inr
              apply Or.inl
              apply True.intro
            let assump_39 := assump_8 assump_53
            apply False.elim assump_39
      case inr assump_20 =>
        have assump_54 : (((p5 ∧ p6) ∨ (True ∨ True)) ∨ ((p4 → p6) ∨ (p6 ∨ p7))) := by
          apply Or.inl
          apply Or.inr
          apply Or.inl
          apply True.intro
        let assump_47 := assump_8 assump_54
        apply False.elim assump_47


variable (p2 p6 p1 p5 p0 p4 p7 p3 : Prop)
theorem file93_110416 : (((((p1 → p6) ∧ (p2 ∧ p1)) ∧ ((p7 ∧ True) → False)) → (((False → False) ∨ (p0 ∧ p5)) ∨ ((False → False) → (p4 → p1)))) ∨ ((((p7 ∧ p2) ∨ (p4 ∧ p4)) → False) ∧ (((p1 → False) ∨ (p7 ∧ p0)) → ((p0 ∧ p2) → (p3 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        apply Or.inl
        apply Or.inl
        intro assump_16
        apply False.elim assump_16


variable (p5 p1 p4 p0 p2 p3 p6 p7 : Prop)
theorem file93_111004 : (((((p5 ∨ False) ∧ (True → False)) ∧ ((p0 ∧ p3) → False)) → False) ∨ ((((p6 ∧ p6) ∧ (True → False)) → False) ∧ (((p1 ∨ p2) ∨ (p1 → p4)) ∨ ((p3 ∨ True) → (p7 ∧ True))))) := by
  apply Or.inl
  intro assump_20
  cases assump_20
  case intro assump_21 assump_22 =>
    cases assump_21
    case intro assump_23 assump_24 =>
      cases assump_23
      case inl assump_25 =>
        have assump_40 : True := by
          apply True.intro
        let assump_34 := assump_24 assump_40
        apply False.elim assump_34
      case inr assump_26 =>
        apply False.elim assump_26


variable (p1 p7 p2 : Prop)
theorem file93_111631 : (((((p1 ∨ p7) ∨ (p1 → False)) ∨ ((True → False) ∧ (p2 → p7))) → False) → False) := by
  intro assump_1
  have assump_16 : (((p1 ∨ p7) ∨ (p1 → False)) ∨ ((True → False) ∧ (p2 → p7))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    have assump_17 : (((p1 ∨ p7) ∨ (p1 → False)) ∨ ((True → False) ∧ (p2 → p7))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p7 : Prop)
theorem file93_112216 : ((((((p7 → False) → (False → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p7 → False) → (False → False)) → False) → False) := by
    intro assump_5
    have assump_20 : ((p7 → False) → (False → False)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_5 assump_20
    apply False.elim assump_8
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p6 p3 p1 p7 p0 : Prop)
theorem file93_112736 : ((((((p6 ∧ p3) → (p1 ∨ p3)) ∨ ((True → False) ∧ (p3 ∧ p6))) ∨ (((True ∧ p3) ∨ (p6 ∧ p0)) ∨ ((True → p7) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p6 ∧ p3) → (p1 ∨ p3)) ∨ ((True → False) ∧ (p3 ∧ p6))) ∨ (((True ∧ p3) ∨ (p6 ∧ p0)) ∨ ((True → p7) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      exact assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p1 p7 p5 p0 p4 p6 : Prop)
theorem file93_113303 : ((((((True → p6) → False) ∧ ((p6 → False) ∧ (False → p7))) → (((p1 ∨ False) ∨ (p5 → p4)) → ((True ∨ p1) ∨ (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_40 : ((((True → p6) → False) ∧ ((p6 → False) ∧ (False → p7))) → (((p1 ∨ False) ∨ (p5 → p4)) → ((True ∨ p1) ∨ (p0 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_5
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
      case inr assump_10 =>
        apply False.elim assump_10
    case inr assump_8 =>
      cases assump_5
      case intro assump_27 assump_28 =>
        cases assump_28
        case intro assump_31 assump_32 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p0 p7 p2 : Prop)
theorem file93_114359 : ((((((True → False) ∨ (p2 → p0)) ∧ ((p7 → True) ∧ (True → False))) → False) → False) → False) := by
  intro assump_1
  have assump_37 : ((((True → False) ∨ (p2 → p0)) ∧ ((p7 → True) ∧ (True → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          have assump_38 : True := by
            apply True.intro
          let assump_18 := assump_13 assump_38
          apply False.elim assump_18
      case inr assump_9 =>
        cases assump_7
        case intro assump_24 assump_25 =>
          have assump_39 : True := by
            apply True.intro
          let assump_30 := assump_25 assump_39
          apply False.elim assump_30
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p0 p4 p5 p2 p7 p6 p1 p3 : Prop)
theorem file93_115287 : (((((p0 ∨ p4) ∨ (p6 → p7)) → False) → (((p4 → p7) ∧ (p4 → False)) ∨ ((p2 → False) ∧ (p0 ∧ p3)))) ∨ ((((p1 ∨ p5) → (False ∧ False)) → False) ∧ (((p5 ∧ p0) ∨ (False → True)) ∧ ((p4 ∨ True) ∧ (False → p1))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_20 : ((p0 ∨ p4) ∨ (p6 → p7)) := by
    apply Or.inl
    apply Or.inr
    exact assump_4
  let assump_8 := assump_1 assump_20
  apply False.elim assump_8
  intro assump_12
  have assump_21 : ((p0 ∨ p4) ∨ (p6 → p7)) := by
    apply Or.inl
    apply Or.inr
    exact assump_12
  let assump_16 := assump_1 assump_21
  apply False.elim assump_16


variable (p6 p1 p4 p2 p7 p5 : Prop)
theorem file93_115996 : ((((((p6 ∨ True) ∧ (p4 → False)) → ((p2 → True) → (p5 ∧ p6))) ∧ (((p4 ∨ p7) → False) → False)) ∧ ((((p6 → False) ∧ (p7 → p5)) ∧ ((True → False) ∧ (p7 → False))) ∧ (((p2 → p6) → (True ∨ p1)) → False))) → False) := by
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
              have assump_35 : ((p2 → p6) → (True ∨ p1)) := by
                intro assump_29
                apply Or.inl
                apply True.intro
              let assump_28 := assump_11 assump_35
              apply False.elim assump_28


variable (p1 p5 p7 p0 p4 : Prop)
theorem file93_116912 : ((((((p1 → p4) → (p7 ∧ True)) ∧ ((p5 ∧ False) ∧ (True ∨ p0))) → False) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p1 → p4) → (p7 ∧ True)) ∧ ((p5 ∧ False) ∧ (True ∨ p0))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p6 p4 p2 p3 p7 p1 p5 p0 : Prop)
theorem file93_117487 : (((((p1 → False) ∨ (p6 → p6)) ∧ ((p2 → p2) → False)) ∧ (((False ∨ p7) ∨ (p0 ∨ p7)) ∧ ((False ∧ p6) → False))) → ((((True ∧ False) ∨ (p4 → False)) ∧ ((p3 → False) ∨ (p3 ∨ p0))) ∧ (((p3 → p3) → (p5 ∧ p0)) → False))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_14
            case inl assump_16 =>
              apply False.elim assump_16
            case inr assump_17 =>
              apply Or.inr
              intro assump_24
              have assump_389 : (p2 → p2) := by
                intro assump_31
                exact assump_31
              let assump_30 := assump_5 assump_389
              apply False.elim assump_30
          case inr assump_15 =>
            cases assump_15
            case inl assump_37 =>
              apply Or.inr
              intro assump_43
              have assump_390 : (p2 → p2) := by
                intro assump_50
                exact assump_50
              let assump_49 := assump_5 assump_390
              apply False.elim assump_49
            case inr assump_38 =>
              apply Or.inr
              intro assump_60
              have assump_391 : (p2 → p2) := by
                intro assump_67
                exact assump_67
              let assump_66 := assump_5 assump_391
              apply False.elim assump_66
      case inr assump_7 =>
        cases assump_3
        case intro assump_77 assump_78 =>
          cases assump_77
          case inl assump_79 =>
            cases assump_79
            case inl assump_81 =>
              apply False.elim assump_81
            case inr assump_82 =>
              apply Or.inr
              intro assump_89
              have assump_392 : (p2 → p2) := by
                intro assump_96
                exact assump_96
              let assump_95 := assump_5 assump_392
              apply False.elim assump_95
          case inr assump_80 =>
            cases assump_80
            case inl assump_102 =>
              apply Or.inr
              intro assump_108
              have assump_393 : (p2 → p2) := by
                intro assump_115
                exact assump_115
              let assump_114 := assump_5 assump_393
              apply False.elim assump_114
            case inr assump_103 =>
              apply Or.inr
              intro assump_125
              have assump_394 : (p2 → p2) := by
                intro assump_132
                exact assump_132
              let assump_131 := assump_5 assump_394
              apply False.elim assump_131
  cases assump_1
  case intro assump_138 assump_139 =>
    cases assump_138
    case intro assump_140 assump_141 =>
      cases assump_140
      case inl assump_142 =>
        cases assump_139
        case intro assump_148 assump_149 =>
          cases assump_148
          case inl assump_150 =>
            cases assump_150
            case inl assump_152 =>
              apply False.elim assump_152
            case inr assump_153 =>
              apply Or.inl
              intro assump_160
              have assump_395 : (p2 → p2) := by
                intro assump_167
                exact assump_167
              let assump_166 := assump_141 assump_395
              apply False.elim assump_166
          case inr assump_151 =>
            cases assump_151
            case inl assump_173 =>
              apply Or.inl
              intro assump_179
              have assump_396 : (p2 → p2) := by
                intro assump_186
                exact assump_186
              let assump_185 := assump_141 assump_396
              apply False.elim assump_185
            case inr assump_174 =>
              apply Or.inl
              intro assump_196
              have assump_397 : (p2 → p2) := by
                intro assump_203
                exact assump_203
              let assump_202 := assump_141 assump_397
              apply False.elim assump_202
      case inr assump_143 =>
        cases assump_139
        case intro assump_213 assump_214 =>
          cases assump_213
          case inl assump_215 =>
            cases assump_215
            case inl assump_217 =>
              apply False.elim assump_217
            case inr assump_218 =>
              apply Or.inl
              intro assump_225
              have assump_398 : (p2 → p2) := by
                intro assump_232
                exact assump_232
              let assump_231 := assump_141 assump_398
              apply False.elim assump_231
          case inr assump_216 =>
            cases assump_216
            case inl assump_238 =>
              apply Or.inl
              intro assump_244
              have assump_399 : (p2 → p2) := by
                intro assump_251
                exact assump_251
              let assump_250 := assump_141 assump_399
              apply False.elim assump_250
            case inr assump_239 =>
              apply Or.inl
              intro assump_261
              have assump_400 : (p2 → p2) := by
                intro assump_268
                exact assump_268
              let assump_267 := assump_141 assump_400
              apply False.elim assump_267
  intro assump_274
  cases assump_1
  case intro assump_277 assump_278 =>
    cases assump_277
    case intro assump_279 assump_280 =>
      cases assump_279
      case inl assump_281 =>
        cases assump_278
        case intro assump_287 assump_288 =>
          cases assump_287
          case inl assump_289 =>
            cases assump_289
            case inl assump_291 =>
              apply False.elim assump_291
            case inr assump_292 =>
              have assump_401 : (p2 → p2) := by
                intro assump_302
                exact assump_302
              let assump_301 := assump_280 assump_401
              apply False.elim assump_301
          case inr assump_290 =>
            cases assump_290
            case inl assump_308 =>
              have assump_402 : (p2 → p2) := by
                intro assump_317
                exact assump_317
              let assump_316 := assump_280 assump_402
              apply False.elim assump_316
            case inr assump_309 =>
              have assump_403 : (p2 → p2) := by
                intro assump_330
                exact assump_330
              let assump_329 := assump_280 assump_403
              apply False.elim assump_329
      case inr assump_282 =>
        cases assump_278
        case intro assump_340 assump_341 =>
          cases assump_340
          case inl assump_342 =>
            cases assump_342
            case inl assump_344 =>
              apply False.elim assump_344
            case inr assump_345 =>
              have assump_404 : (p2 → p2) := by
                intro assump_355
                exact assump_355
              let assump_354 := assump_280 assump_404
              apply False.elim assump_354
          case inr assump_343 =>
            cases assump_343
            case inl assump_361 =>
              have assump_405 : (p2 → p2) := by
                intro assump_370
                exact assump_370
              let assump_369 := assump_280 assump_405
              apply False.elim assump_369
            case inr assump_362 =>
              have assump_406 : (p2 → p2) := by
                intro assump_383
                exact assump_383
              let assump_382 := assump_280 assump_406
              apply False.elim assump_382


variable (p1 p0 p5 p7 p3 p2 p6 : Prop)
theorem file93_125247 : (((((False → False) → False) ∧ ((p6 → False) ∨ (p6 ∨ p5))) → (((p0 ∧ False) ∨ (p2 ∧ False)) ∧ ((p5 ∧ p1) → (p3 ∨ False)))) → ((((p1 → False) → False) ∧ ((p2 ∧ p6) → (p7 → p1))) → (((p2 → False) → (False → False)) ∨ ((p5 → False) ∧ (p2 ∨ p0))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inl
    intro assump_11
    intro assump_12
    apply False.elim assump_12


variable (p2 p7 p3 p0 p4 : Prop)
theorem file93_125728 : ((((((p0 ∨ True) → False) → ((p2 ∧ False) → False)) → False) ∧ ((((p4 ∨ p4) ∧ (p0 ∨ p7)) → ((p3 ∨ True) ∧ (p7 → False))) ∨ (((p2 ∨ p0) ∧ (p0 → p4)) ∨ ((p2 ∨ False) ∧ (p2 ∨ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_94 : (((p0 ∨ True) → False) → ((p2 ∧ False) → False)) := by
        intro assump_12
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
      let assump_11 := assump_2 assump_94
      apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case inl assump_23 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          cases assump_25
          case inl assump_27 =>
            have assump_95 : (((p0 ∨ True) → False) → ((p2 ∧ False) → False)) := by
              intro assump_36
              intro assump_37
              cases assump_37
              case intro assump_38 assump_39 =>
                apply False.elim assump_39
            let assump_35 := assump_2 assump_95
            apply False.elim assump_35
          case inr assump_28 =>
            have assump_96 : (((p0 ∨ True) → False) → ((p2 ∧ False) → False)) := by
              intro assump_55
              intro assump_56
              cases assump_56
              case intro assump_57 assump_58 =>
                apply False.elim assump_58
            let assump_54 := assump_2 assump_96
            apply False.elim assump_54
      case inr assump_24 =>
        cases assump_24
        case intro assump_66 assump_67 =>
          cases assump_66
          case inl assump_68 =>
            cases assump_67
            case inl assump_72 =>
              have assump_97 : (((p0 ∨ True) → False) → ((p2 ∧ False) → False)) := by
                intro assump_79
                intro assump_80
                cases assump_80
                case intro assump_81 assump_82 =>
                  apply False.elim assump_82
              let assump_78 := assump_2 assump_97
              apply False.elim assump_78
            case inr assump_73 =>
              apply False.elim assump_73
          case inr assump_69 =>
            apply False.elim assump_69


variable (p2 p7 p5 p1 p3 p0 p4 : Prop)
theorem file93_128067 : ((((((p3 → False) ∧ (p0 ∨ p2)) → False) ∨ (((p7 → False) ∨ (p0 → False)) → False)) ∧ ((((p4 ∧ False) → (p5 → False)) → ((p4 ∨ p5) → (p2 → False))) ∧ (((p1 → p4) → False) ∧ ((p1 ∧ p1) → (p1 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          have assump_58 : (p1 → p4) := by
            intro assump_20
            have assump_59 : (p1 ∧ p1) := by
              apply And.intro
              exact assump_20
              exact assump_20
            let assump_24 := assump_13 assump_59
            have assump_60 : p1 := by
              exact assump_20
            let assump_25 := assump_24 assump_60
            apply False.elim assump_25
          let assump_19 := assump_12 assump_58
          apply False.elim assump_19
    case inr assump_5 =>
      cases assump_3
      case intro assump_34 assump_35 =>
        cases assump_35
        case intro assump_38 assump_39 =>
          have assump_61 : (p1 → p4) := by
            intro assump_46
            have assump_62 : (p1 ∧ p1) := by
              apply And.intro
              exact assump_46
              exact assump_46
            let assump_50 := assump_39 assump_62
            have assump_63 : p1 := by
              exact assump_46
            let assump_51 := assump_50 assump_63
            apply False.elim assump_51
          let assump_45 := assump_38 assump_61
          apply False.elim assump_45


