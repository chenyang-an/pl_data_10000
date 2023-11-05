variable (p5 p2 p7 p3 p4 p1 p0 : Prop)
theorem file59_47 : (((((p5 → False) ∧ (p5 ∧ p2)) ∨ ((p1 ∧ p2) ∧ (p7 → False))) ∧ (((True ∨ p0) → False) ∧ ((p4 ∨ p1) → (p0 ∧ p4)))) → ((((p1 ∧ p0) → (p7 → False)) → False) ∧ (((p5 ∧ False) → False) ∧ ((p7 → False) ∨ (p3 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_10
        case intro assump_13 assump_14 =>
          cases assump_6
          case intro assump_19 assump_20 =>
            have assump_118 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_26 := assump_19 assump_118
            apply False.elim assump_26
    case inr assump_8 =>
      cases assump_8
      case intro assump_30 assump_31 =>
        cases assump_30
        case intro assump_32 assump_33 =>
          cases assump_6
          case intro assump_40 assump_41 =>
            have assump_119 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_50 := assump_40 assump_119
            apply False.elim assump_50
  apply And.intro
  intro assump_54
  cases assump_54
  case intro assump_55 assump_56 =>
    apply False.elim assump_56
  cases assump_1
  case intro assump_61 assump_62 =>
    cases assump_61
    case inl assump_63 =>
      cases assump_63
      case intro assump_65 assump_66 =>
        cases assump_66
        case intro assump_69 assump_70 =>
          cases assump_62
          case intro assump_75 assump_76 =>
            apply Or.inl
            intro assump_81
            have assump_120 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_86 := assump_75 assump_120
            apply False.elim assump_86
    case inr assump_64 =>
      cases assump_64
      case intro assump_90 assump_91 =>
        cases assump_90
        case intro assump_92 assump_93 =>
          cases assump_62
          case intro assump_100 assump_101 =>
            apply Or.inl
            intro assump_106
            have assump_121 : (True ∨ p0) := by
              apply Or.inl
              apply True.intro
            let assump_114 := assump_100 assump_121
            apply False.elim assump_114


variable (p4 p0 p5 p2 p1 p6 : Prop)
theorem file59_2424 : ((((((False ∧ p1) ∧ (p1 ∨ p5)) → ((True → False) → False)) → (((p6 ∨ p4) ∧ (p0 ∨ p2)) → ((True → False) → (p4 ∧ p1)))) → ((((p2 ∨ p6) ∨ (p1 ∧ True)) ∨ ((p0 ∧ False) → False)) → False)) → False) := by
  intro assump_1
  have assump_121 : ((((False ∧ p1) ∧ (p1 ∨ p5)) → ((True → False) → False)) → (((p6 ∨ p4) ∧ (p0 ∨ p2)) → ((True → False) → (p4 ∧ p1)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply And.intro
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_11
        case inl assump_16 =>
          have assump_122 : True := by
            apply True.intro
          let assump_25 := assump_7 assump_122
          apply False.elim assump_25
        case inr assump_17 =>
          have assump_123 : True := by
            apply True.intro
          let assump_36 := assump_7 assump_123
          apply False.elim assump_36
      case inr assump_13 =>
        cases assump_11
        case inl assump_42 =>
          exact assump_13
        case inr assump_43 =>
          exact assump_13
    cases assump_6
    case intro assump_54 assump_55 =>
      cases assump_54
      case inl assump_56 =>
        cases assump_55
        case inl assump_60 =>
          have assump_124 : True := by
            apply True.intro
          let assump_69 := assump_7 assump_124
          apply False.elim assump_69
        case inr assump_61 =>
          have assump_125 : True := by
            apply True.intro
          let assump_80 := assump_7 assump_125
          apply False.elim assump_80
      case inr assump_57 =>
        cases assump_55
        case inl assump_86 =>
          have assump_126 : True := by
            apply True.intro
          let assump_95 := assump_7 assump_126
          apply False.elim assump_95
        case inr assump_87 =>
          have assump_127 : True := by
            apply True.intro
          let assump_106 := assump_7 assump_127
          apply False.elim assump_106
  let assump_4 := assump_1 assump_121
  have assump_128 : (((p2 ∨ p6) ∨ (p1 ∧ True)) ∨ ((p0 ∧ False) → False)) := by
    apply Or.inr
    intro assump_111
    cases assump_111
    case intro assump_112 assump_113 =>
      apply False.elim assump_113
  let assump_110 := assump_4 assump_128
  apply False.elim assump_110


variable (p3 p0 p2 p1 : Prop)
theorem file59_4807 : ((((((p1 → False) → (p1 ∨ p3)) → ((True → False) ∨ (p1 → False))) ∨ (((p0 → False) → False) → False)) ∧ ((((True → False) → (p2 ∨ p0)) ∨ ((p3 → False) ∨ (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_36 : (((True → False) → (p2 ∨ p0)) ∨ ((p3 → False) ∨ (False → False))) := by
        apply Or.inl
        intro assump_11
        have assump_37 : True := by
          apply True.intro
        let assump_14 := assump_11 assump_37
        apply False.elim assump_14
      let assump_10 := assump_3 assump_36
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_38 : (((True → False) → (p2 ∨ p0)) ∨ ((p3 → False) ∨ (False → False))) := by
        apply Or.inl
        intro assump_26
        have assump_39 : True := by
          apply True.intro
        let assump_29 := assump_26 assump_39
        apply False.elim assump_29
      let assump_25 := assump_3 assump_38
      apply False.elim assump_25


variable (p5 p6 p0 p1 p4 p7 p3 : Prop)
theorem file59_5919 : (((((p7 → False) ∧ (p3 ∧ p4)) ∧ ((p0 ∨ True) → False)) ∧ (((True → False) ∨ (p0 → p1)) → ((p0 → False) → (p4 → p3)))) → ((((True → p5) → (p6 → False)) → False) → (((p5 → True) → False) → ((p4 ∧ p5) → (p7 ∨ p3))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_1
    case intro assump_15 assump_16 =>
      cases assump_15
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          cases assump_20
          case intro assump_23 assump_24 =>
            apply Or.inr
            exact assump_23


variable (p7 p2 p6 p1 p3 p4 : Prop)
theorem file59_6626 : (((((p7 → p4) ∨ (p1 ∨ p3)) → ((p4 → False) ∧ (p4 → False))) ∧ (((p1 ∧ p2) ∧ (p6 → False)) ∧ ((p7 ∨ p4) → False))) → ((((p2 → False) ∧ (p1 ∨ p1)) ∨ ((p7 ∧ True) ∧ (True → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case inl assump_9 =>
        cases assump_1
        case intro assump_13 assump_14 =>
          cases assump_14
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_19
              case intro assump_21 assump_22 =>
                have assump_125 : p2 := by
                  exact assump_22
                let assump_48 := assump_5 assump_125
                apply False.elim assump_48
      case inr assump_10 =>
        cases assump_1
        case intro assump_54 assump_55 =>
          cases assump_55
          case intro assump_58 assump_59 =>
            cases assump_58
            case intro assump_60 assump_61 =>
              cases assump_60
              case intro assump_62 assump_63 =>
                have assump_126 : p2 := by
                  exact assump_63
                let assump_89 := assump_5 assump_126
                apply False.elim assump_89
  case inr assump_4 =>
    cases assump_4
    case intro assump_93 assump_94 =>
      cases assump_93
      case intro assump_95 assump_96 =>
        cases assump_1
        case intro assump_103 assump_104 =>
          cases assump_104
          case intro assump_107 assump_108 =>
            cases assump_107
            case intro assump_109 assump_110 =>
              cases assump_109
              case intro assump_111 assump_112 =>
                have assump_127 : (p7 ∨ p4) := by
                  apply Or.inl
                  exact assump_95
                let assump_121 := assump_108 assump_127
                apply False.elim assump_121


variable (p0 p3 p2 p6 p4 p5 p1 : Prop)
theorem file59_8664 : (((((True → p4) → (p3 ∧ p2)) → ((True ∨ p2) ∨ (p1 ∧ p3))) ∨ (((p5 → p1) ∧ (False ∨ p4)) ∧ ((p4 ∨ False) → (p4 → False)))) → ((((p6 ∨ p2) → (p3 ∧ p2)) → ((False ∧ p2) → (p0 ∧ p1))) → (((p5 ∧ p0) ∧ (p0 → p6)) → ((p2 → True) ∨ (p3 ∨ p0))))) := by
  intro assump_20
  intro assump_21
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    cases assump_23
    case intro assump_25 assump_26 =>
      cases assump_20
      case inl assump_35 =>
        apply Or.inl
        intro assump_39
        apply True.intro
      case inr assump_36 =>
        cases assump_36
        case intro assump_40 assump_41 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            cases assump_43
            case inl assump_46 =>
              apply False.elim assump_46
            case inr assump_47 =>
              apply Or.inl
              intro assump_54
              apply True.intro


variable (p3 p2 p7 p6 p1 p4 : Prop)
theorem file59_9643 : ((((((p3 → p3) → (p2 → False)) ∨ ((p1 ∧ p7) ∧ (p4 → p4))) → (((p4 ∨ p4) ∨ (p1 → p6)) → ((p7 → False) → (False → p1)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p3 → p3) → (p2 → False)) ∨ ((p1 ∧ p7) ∧ (p4 → p4))) → (((p4 ∨ p4) ∨ (p1 → p6)) → ((p7 → False) → (False → p1)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p0 p7 p3 p2 : Prop)
theorem file59_10170 : (((((p0 ∨ p2) → (True ∨ p3)) ∨ ((p0 → p7) ∧ (p3 → False))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p0 ∨ p2) → (True ∨ p3)) ∨ ((p0 → p7) ∧ (p3 → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p1 p0 p3 : Prop)
theorem file59_10660 : ((((((False → False) ∧ (p0 → p0)) ∨ ((p1 ∧ True) → False)) → False) ∨ ((((p4 → p4) ∨ (p3 ∨ p1)) → ((False → False) ∨ (p3 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_42 : (((False → False) ∧ (p0 → p0)) ∨ ((p1 ∧ True) → False)) := by
      apply Or.inl
      apply And.intro
      intro assump_7
      apply False.elim assump_7
      intro assump_10
      exact assump_10
    let assump_6 := assump_2 assump_42
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_43 : (((p4 → p4) ∨ (p3 ∨ p1)) → ((False → False) ∨ (p3 → False))) := by
      intro assump_19
      cases assump_19
      case inl assump_20 =>
        apply Or.inl
        intro assump_24
        apply False.elim assump_24
      case inr assump_21 =>
        cases assump_21
        case inl assump_27 =>
          apply Or.inl
          intro assump_31
          apply False.elim assump_31
        case inr assump_28 =>
          apply Or.inl
          intro assump_36
          apply False.elim assump_36
    let assump_18 := assump_3 assump_43
    apply False.elim assump_18


variable (p5 p2 p1 p6 p3 p4 p0 p7 : Prop)
theorem file59_11848 : (((((p6 ∨ p2) ∧ (p0 → False)) → ((p0 ∨ p2) ∨ (p0 → False))) → False) → ((((p5 ∨ p7) ∨ (p0 ∧ False)) → ((p7 → p2) → False)) → (((p7 → p2) ∨ (p2 ∨ p5)) ∨ ((p4 ∨ p1) → (p3 → p7))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inl
  intro assump_7
  have assump_36 : (((p6 ∨ p2) ∧ (p0 → False)) → ((p0 ∨ p2) ∨ (p0 → False))) := by
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      cases assump_13
      case inl assump_15 =>
        apply Or.inr
        intro assump_21
        have assump_37 : p0 := by
          exact assump_21
        let assump_25 := assump_14 assump_37
        apply False.elim assump_25
      case inr assump_16 =>
        apply Or.inl
        apply Or.inr
        exact assump_16
  let assump_11 := assump_1 assump_36
  apply False.elim assump_11


variable (p4 p7 p3 p6 p5 : Prop)
theorem file59_12728 : (((((p6 → p4) → False) → False) → False) → ((((p4 → False) → False) ∧ ((False ∧ p5) ∧ (p3 → False))) → (((True ∨ True) ∨ (p3 ∧ p7)) → False))) := by
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_7
  case inl assump_8 =>
    cases assump_8
    case inl assump_10 =>
      cases assump_6
      case intro assump_14 assump_15 =>
        cases assump_15
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            apply False.elim assump_20
    case inr assump_11 =>
      cases assump_6
      case intro assump_26 assump_27 =>
        cases assump_27
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            apply False.elim assump_32
  case inr assump_9 =>
    cases assump_9
    case intro assump_36 assump_37 =>
      cases assump_6
      case intro assump_42 assump_43 =>
        cases assump_43
        case intro assump_46 assump_47 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            apply False.elim assump_48


variable (p4 p6 p5 p1 : Prop)
theorem file59_13881 : (((((p1 ∧ p6) ∧ (p5 ∨ p5)) → ((True → True) ∨ (False ∧ p4))) → False) → False) := by
  intro assump_1
  have assump_25 : (((p1 ∧ p6) ∧ (p5 ∨ p5)) → ((True → True) ∨ (False ∧ p4))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply Or.inl
          intro assump_18
          apply True.intro
        case inr assump_15 =>
          apply Or.inl
          intro assump_21
          apply True.intro
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p4 p6 p0 p3 p2 p1 p5 p7 : Prop)
theorem file59_14566 : (((((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) → False) → ((((True → p2) ∨ (p0 → False)) ∧ ((p5 ∧ p0) ∨ (p1 → False))) → (((False ∨ p6) → (p4 ∧ p3)) ∧ ((True ∨ p4) → False)))) := by
  intro assump_9
  intro assump_10
  apply And.intro
  intro assump_11
  apply And.intro
  cases assump_11
  case inl assump_12 =>
    apply False.elim assump_12
  case inr assump_13 =>
    cases assump_10
    case intro assump_18 assump_19 =>
      cases assump_18
      case inl assump_20 =>
        cases assump_19
        case inl assump_24 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            have assump_283 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
              apply Or.inl
              apply Or.inl
              apply Or.inl
              exact assump_13
            let assump_34 := assump_9 assump_283
            apply False.elim assump_34
        case inr assump_25 =>
          have assump_284 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
            apply Or.inl
            apply Or.inl
            apply Or.inl
            exact assump_13
          let assump_42 := assump_9 assump_284
          apply False.elim assump_42
      case inr assump_21 =>
        cases assump_19
        case inl assump_48 =>
          cases assump_48
          case intro assump_50 assump_51 =>
            have assump_285 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
              apply Or.inl
              apply Or.inl
              apply Or.inl
              exact assump_13
            let assump_58 := assump_9 assump_285
            apply False.elim assump_58
        case inr assump_49 =>
          have assump_286 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
            apply Or.inl
            apply Or.inl
            apply Or.inl
            exact assump_13
          let assump_66 := assump_9 assump_286
          apply False.elim assump_66
  cases assump_11
  case inl assump_70 =>
    apply False.elim assump_70
  case inr assump_71 =>
    cases assump_10
    case intro assump_76 assump_77 =>
      cases assump_76
      case inl assump_78 =>
        cases assump_77
        case inl assump_82 =>
          cases assump_82
          case intro assump_84 assump_85 =>
            have assump_287 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
              apply Or.inl
              apply Or.inl
              apply Or.inl
              exact assump_71
            let assump_92 := assump_9 assump_287
            apply False.elim assump_92
        case inr assump_83 =>
          have assump_288 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
            apply Or.inl
            apply Or.inl
            apply Or.inl
            exact assump_71
          let assump_100 := assump_9 assump_288
          apply False.elim assump_100
      case inr assump_79 =>
        cases assump_77
        case inl assump_106 =>
          cases assump_106
          case intro assump_108 assump_109 =>
            have assump_289 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
              apply Or.inl
              apply Or.inl
              apply Or.inl
              exact assump_71
            let assump_116 := assump_9 assump_289
            apply False.elim assump_116
        case inr assump_107 =>
          have assump_290 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
            apply Or.inl
            apply Or.inl
            apply Or.inl
            exact assump_71
          let assump_124 := assump_9 assump_290
          apply False.elim assump_124
  intro assump_128
  cases assump_128
  case inl assump_129 =>
    cases assump_10
    case intro assump_133 assump_134 =>
      cases assump_133
      case inl assump_135 =>
        cases assump_134
        case inl assump_139 =>
          cases assump_139
          case intro assump_141 assump_142 =>
            have assump_291 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
              apply Or.inl
              apply Or.inr
              intro assump_150
              have assump_292 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
                apply Or.inl
                apply Or.inl
                apply Or.inl
                exact assump_150
              let assump_154 := assump_9 assump_292
              apply False.elim assump_154
            let assump_149 := assump_9 assump_291
            apply False.elim assump_149
        case inr assump_140 =>
          have assump_293 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_166
            have assump_294 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
              apply Or.inl
              apply Or.inl
              apply Or.inl
              exact assump_166
            let assump_170 := assump_9 assump_294
            apply False.elim assump_170
          let assump_165 := assump_9 assump_293
          apply False.elim assump_165
      case inr assump_136 =>
        cases assump_134
        case inl assump_179 =>
          cases assump_179
          case intro assump_181 assump_182 =>
            have assump_295 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
              apply Or.inl
              apply Or.inr
              intro assump_190
              have assump_296 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
                apply Or.inl
                apply Or.inl
                apply Or.inl
                exact assump_190
              let assump_194 := assump_9 assump_296
              apply False.elim assump_194
            let assump_189 := assump_9 assump_295
            apply False.elim assump_189
        case inr assump_180 =>
          have assump_297 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_206
            have assump_298 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
              apply Or.inl
              apply Or.inl
              apply Or.inl
              exact assump_206
            let assump_210 := assump_9 assump_298
            apply False.elim assump_210
          let assump_205 := assump_9 assump_297
          apply False.elim assump_205
  case inr assump_130 =>
    cases assump_10
    case intro assump_219 assump_220 =>
      cases assump_219
      case inl assump_221 =>
        cases assump_220
        case inl assump_225 =>
          cases assump_225
          case intro assump_227 assump_228 =>
            have assump_299 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
              apply Or.inl
              apply Or.inr
              intro assump_236
              exact assump_130
            let assump_235 := assump_9 assump_299
            apply False.elim assump_235
        case inr assump_226 =>
          have assump_300 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_247
            exact assump_130
          let assump_246 := assump_9 assump_300
          apply False.elim assump_246
      case inr assump_222 =>
        cases assump_220
        case inl assump_255 =>
          cases assump_255
          case intro assump_257 assump_258 =>
            have assump_301 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
              apply Or.inl
              apply Or.inr
              intro assump_266
              exact assump_130
            let assump_265 := assump_9 assump_301
            apply False.elim assump_265
        case inr assump_256 =>
          have assump_302 : (((p6 ∨ p7) ∨ (p6 → p4)) ∨ ((p1 ∧ p2) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_277
            exact assump_130
          let assump_276 := assump_9 assump_302
          apply False.elim assump_276


variable (p6 p5 p2 p1 p0 p7 p3 : Prop)
theorem file59_22530 : ((((((p7 → False) ∨ (p2 ∧ True)) ∧ ((p1 → False) ∧ (p7 ∨ p5))) ∨ (((p3 ∨ p3) → (p7 ∨ p7)) ∧ ((p3 ∧ p5) → (p3 ∨ False)))) ∧ ((((p6 ∧ p1) → (p0 ∧ p3)) ∧ ((False → False) → False)) ∧ (((True ∨ True) ∧ (p6 → p0)) ∨ ((p7 ∨ False) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_7
          case intro assump_12 assump_13 =>
            cases assump_13
            case inl assump_16 =>
              cases assump_3
              case intro assump_20 assump_21 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  cases assump_21
                  case inl assump_28 =>
                    cases assump_28
                    case intro assump_30 assump_31 =>
                      cases assump_30
                      case inl assump_32 =>
                        have assump_276 : (False → False) := by
                          intro assump_40
                          apply False.elim assump_40
                        let assump_39 := assump_23 assump_276
                        apply False.elim assump_39
                      case inr assump_33 =>
                        have assump_277 : (False → False) := by
                          intro assump_52
                          apply False.elim assump_52
                        let assump_51 := assump_23 assump_277
                        apply False.elim assump_51
                  case inr assump_29 =>
                    have assump_278 : (p7 ∨ False) := by
                      apply Or.inl
                      exact assump_16
                    let assump_60 := assump_29 assump_278
                    apply False.elim assump_60
            case inr assump_17 =>
              cases assump_3
              case intro assump_66 assump_67 =>
                cases assump_66
                case intro assump_68 assump_69 =>
                  cases assump_67
                  case inl assump_74 =>
                    cases assump_74
                    case intro assump_76 assump_77 =>
                      cases assump_76
                      case inl assump_78 =>
                        have assump_279 : (False → False) := by
                          intro assump_86
                          apply False.elim assump_86
                        let assump_85 := assump_69 assump_279
                        apply False.elim assump_85
                      case inr assump_79 =>
                        have assump_280 : (False → False) := by
                          intro assump_98
                          apply False.elim assump_98
                        let assump_97 := assump_69 assump_280
                        apply False.elim assump_97
                  case inr assump_75 =>
                    have assump_281 : (False → False) := by
                      intro assump_108
                      apply False.elim assump_108
                    let assump_107 := assump_69 assump_281
                    apply False.elim assump_107
        case inr assump_9 =>
          cases assump_9
          case intro assump_114 assump_115 =>
            cases assump_7
            case intro assump_120 assump_121 =>
              cases assump_121
              case inl assump_124 =>
                cases assump_3
                case intro assump_128 assump_129 =>
                  cases assump_128
                  case intro assump_130 assump_131 =>
                    cases assump_129
                    case inl assump_136 =>
                      cases assump_136
                      case intro assump_138 assump_139 =>
                        cases assump_138
                        case inl assump_140 =>
                          have assump_282 : (False → False) := by
                            intro assump_148
                            apply False.elim assump_148
                          let assump_147 := assump_131 assump_282
                          apply False.elim assump_147
                        case inr assump_141 =>
                          have assump_283 : (False → False) := by
                            intro assump_160
                            apply False.elim assump_160
                          let assump_159 := assump_131 assump_283
                          apply False.elim assump_159
                    case inr assump_137 =>
                      have assump_284 : (p7 ∨ False) := by
                        apply Or.inl
                        exact assump_124
                      let assump_168 := assump_137 assump_284
                      apply False.elim assump_168
              case inr assump_125 =>
                cases assump_3
                case intro assump_174 assump_175 =>
                  cases assump_174
                  case intro assump_176 assump_177 =>
                    cases assump_175
                    case inl assump_182 =>
                      cases assump_182
                      case intro assump_184 assump_185 =>
                        cases assump_184
                        case inl assump_186 =>
                          have assump_285 : (False → False) := by
                            intro assump_194
                            apply False.elim assump_194
                          let assump_193 := assump_177 assump_285
                          apply False.elim assump_193
                        case inr assump_187 =>
                          have assump_286 : (False → False) := by
                            intro assump_206
                            apply False.elim assump_206
                          let assump_205 := assump_177 assump_286
                          apply False.elim assump_205
                    case inr assump_183 =>
                      have assump_287 : (False → False) := by
                        intro assump_216
                        apply False.elim assump_216
                      let assump_215 := assump_177 assump_287
                      apply False.elim assump_215
    case inr assump_5 =>
      cases assump_5
      case intro assump_222 assump_223 =>
        cases assump_3
        case intro assump_228 assump_229 =>
          cases assump_228
          case intro assump_230 assump_231 =>
            cases assump_229
            case inl assump_236 =>
              cases assump_236
              case intro assump_238 assump_239 =>
                cases assump_238
                case inl assump_240 =>
                  have assump_288 : (False → False) := by
                    intro assump_248
                    apply False.elim assump_248
                  let assump_247 := assump_231 assump_288
                  apply False.elim assump_247
                case inr assump_241 =>
                  have assump_289 : (False → False) := by
                    intro assump_260
                    apply False.elim assump_260
                  let assump_259 := assump_231 assump_289
                  apply False.elim assump_259
            case inr assump_237 =>
              have assump_290 : (False → False) := by
                intro assump_270
                apply False.elim assump_270
              let assump_269 := assump_231 assump_290
              apply False.elim assump_269


variable (p4 p5 p0 p6 p7 p1 : Prop)
theorem file59_30025 : ((((((p6 ∨ p0) → False) ∨ ((p5 ∧ p6) → False)) → (((p4 ∨ True) ∧ (p7 ∨ p1)) ∨ ((False ∨ p7) → (p4 ∨ True)))) → False) → False) := by
  intro assump_17
  have assump_45 : ((((p6 ∨ p0) → False) ∨ ((p5 ∧ p6) → False)) → (((p4 ∨ True) ∧ (p7 ∨ p1)) ∨ ((False ∨ p7) → (p4 ∨ True)))) := by
    intro assump_21
    cases assump_21
    case inl assump_22 =>
      apply Or.inr
      intro assump_26
      cases assump_26
      case inl assump_27 =>
        apply False.elim assump_27
      case inr assump_28 =>
        apply Or.inr
        apply True.intro
    case inr assump_23 =>
      apply Or.inr
      intro assump_35
      cases assump_35
      case inl assump_36 =>
        apply False.elim assump_36
      case inr assump_37 =>
        apply Or.inr
        apply True.intro
  let assump_20 := assump_17 assump_45
  apply False.elim assump_20


variable (p3 p5 p6 p1 p2 p7 p4 : Prop)
theorem file59_30931 : ((((((p5 ∧ p6) ∧ (False → False)) ∧ ((p1 ∧ False) ∧ (p2 → False))) → (((p2 ∨ p3) ∧ (p4 ∧ False)) ∧ ((p7 ∧ p5) ∨ (p1 → p3)))) → False) → False) := by
  intro assump_1
  have assump_89 : ((((p5 ∧ p6) ∧ (False → False)) ∧ ((p1 ∧ False) ∧ (p2 → False))) → (((p2 ∨ p3) ∧ (p4 ∧ False)) ∧ ((p7 ∧ p5) ∨ (p1 → p3)))) := by
    intro assump_5
    apply And.intro
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              apply False.elim assump_21
    apply And.intro
    cases assump_5
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        cases assump_28
        case intro assump_30 assump_31 =>
          cases assump_27
          case intro assump_38 assump_39 =>
            cases assump_38
            case intro assump_40 assump_41 =>
              apply False.elim assump_41
    cases assump_5
    case intro assump_46 assump_47 =>
      cases assump_46
      case intro assump_48 assump_49 =>
        cases assump_48
        case intro assump_50 assump_51 =>
          cases assump_47
          case intro assump_58 assump_59 =>
            cases assump_58
            case intro assump_60 assump_61 =>
              apply False.elim assump_61
    cases assump_5
    case intro assump_66 assump_67 =>
      cases assump_66
      case intro assump_68 assump_69 =>
        cases assump_68
        case intro assump_70 assump_71 =>
          cases assump_67
          case intro assump_78 assump_79 =>
            cases assump_78
            case intro assump_80 assump_81 =>
              apply False.elim assump_81
  let assump_4 := assump_1 assump_89
  apply False.elim assump_4


variable (p7 p4 p5 p3 p6 p1 p0 p2 : Prop)
theorem file59_32928 : (((((False ∨ False) ∧ (p6 → p6)) ∧ ((p2 ∧ p5) → (p7 → p1))) ∧ (((p0 ∨ p5) ∨ (False ∨ p7)) ∨ ((p6 → False) → False))) → ((((False ∧ p3) ∨ (p4 → p6)) ∨ ((p2 ∧ p0) → (True ∧ p6))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7
    case inr assump_6 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_17
            case inl assump_19 =>
              apply False.elim assump_19
            case inr assump_20 =>
              apply False.elim assump_20
  case inr assump_4 =>
    cases assump_1
    case intro assump_27 assump_28 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          cases assump_31
          case inl assump_33 =>
            apply False.elim assump_33
          case inr assump_34 =>
            apply False.elim assump_34


variable (p4 p1 p5 p6 p0 p7 : Prop)
theorem file59_34168 : ((((((p7 ∨ False) → (p6 ∧ p6)) ∨ ((p6 → p0) → False)) ∨ (((p1 ∨ p7) ∧ (p1 ∧ p6)) → ((False → p5) → False))) ∧ ((((p6 ∧ p1) ∨ (p0 ∧ True)) ∨ ((p1 ∨ p4) ∧ (p1 → False))) ∧ (((p7 ∧ False) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_12
            case inl assump_14 =>
              cases assump_14
              case intro assump_16 assump_17 =>
                have assump_260 : ((p7 ∧ False) → False) := by
                  intro assump_25
                  cases assump_25
                  case intro assump_26 assump_27 =>
                    apply False.elim assump_27
                let assump_24 := assump_11 assump_260
                apply False.elim assump_24
            case inr assump_15 =>
              cases assump_15
              case intro assump_35 assump_36 =>
                have assump_261 : ((p7 ∧ False) → False) := by
                  intro assump_44
                  cases assump_44
                  case intro assump_45 assump_46 =>
                    apply False.elim assump_46
                let assump_43 := assump_11 assump_261
                apply False.elim assump_43
          case inr assump_13 =>
            cases assump_13
            case intro assump_54 assump_55 =>
              cases assump_54
              case inl assump_56 =>
                have assump_262 : ((p7 ∧ False) → False) := by
                  intro assump_65
                  cases assump_65
                  case intro assump_66 assump_67 =>
                    apply False.elim assump_67
                let assump_64 := assump_11 assump_262
                apply False.elim assump_64
              case inr assump_57 =>
                have assump_263 : ((p7 ∧ False) → False) := by
                  intro assump_82
                  cases assump_82
                  case intro assump_83 assump_84 =>
                    apply False.elim assump_84
                let assump_81 := assump_11 assump_263
                apply False.elim assump_81
      case inr assump_7 =>
        cases assump_3
        case intro assump_94 assump_95 =>
          cases assump_94
          case inl assump_96 =>
            cases assump_96
            case inl assump_98 =>
              cases assump_98
              case intro assump_100 assump_101 =>
                have assump_264 : ((p7 ∧ False) → False) := by
                  intro assump_109
                  cases assump_109
                  case intro assump_110 assump_111 =>
                    apply False.elim assump_111
                let assump_108 := assump_95 assump_264
                apply False.elim assump_108
            case inr assump_99 =>
              cases assump_99
              case intro assump_119 assump_120 =>
                have assump_265 : ((p7 ∧ False) → False) := by
                  intro assump_128
                  cases assump_128
                  case intro assump_129 assump_130 =>
                    apply False.elim assump_130
                let assump_127 := assump_95 assump_265
                apply False.elim assump_127
          case inr assump_97 =>
            cases assump_97
            case intro assump_138 assump_139 =>
              cases assump_138
              case inl assump_140 =>
                have assump_266 : ((p7 ∧ False) → False) := by
                  intro assump_149
                  cases assump_149
                  case intro assump_150 assump_151 =>
                    apply False.elim assump_151
                let assump_148 := assump_95 assump_266
                apply False.elim assump_148
              case inr assump_141 =>
                have assump_267 : ((p7 ∧ False) → False) := by
                  intro assump_166
                  cases assump_166
                  case intro assump_167 assump_168 =>
                    apply False.elim assump_168
                let assump_165 := assump_95 assump_267
                apply False.elim assump_165
    case inr assump_5 =>
      cases assump_3
      case intro assump_178 assump_179 =>
        cases assump_178
        case inl assump_180 =>
          cases assump_180
          case inl assump_182 =>
            cases assump_182
            case intro assump_184 assump_185 =>
              have assump_268 : ((p7 ∧ False) → False) := by
                intro assump_193
                cases assump_193
                case intro assump_194 assump_195 =>
                  apply False.elim assump_195
              let assump_192 := assump_179 assump_268
              apply False.elim assump_192
          case inr assump_183 =>
            cases assump_183
            case intro assump_203 assump_204 =>
              have assump_269 : ((p7 ∧ False) → False) := by
                intro assump_212
                cases assump_212
                case intro assump_213 assump_214 =>
                  apply False.elim assump_214
              let assump_211 := assump_179 assump_269
              apply False.elim assump_211
        case inr assump_181 =>
          cases assump_181
          case intro assump_222 assump_223 =>
            cases assump_222
            case inl assump_224 =>
              have assump_270 : ((p7 ∧ False) → False) := by
                intro assump_233
                cases assump_233
                case intro assump_234 assump_235 =>
                  apply False.elim assump_235
              let assump_232 := assump_179 assump_270
              apply False.elim assump_232
            case inr assump_225 =>
              have assump_271 : ((p7 ∧ False) → False) := by
                intro assump_250
                cases assump_250
                case intro assump_251 assump_252 =>
                  apply False.elim assump_252
              let assump_249 := assump_179 assump_271
              apply False.elim assump_249


variable (p1 p6 p5 p7 p0 p4 : Prop)
theorem file59_40332 : (((((p4 ∧ p4) → False) → False) ∧ (((False → True) ∨ (p4 ∨ p7)) → False)) → ((((p5 → False) ∨ (p7 ∨ p0)) ∨ ((p5 ∨ p0) → (p4 → False))) ∨ (((True ∧ True) ∧ (True → p1)) → ((p6 ∧ p5) → (True → p4))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_8
    have assump_17 : ((False → True) ∨ (p4 ∨ p7)) := by
      apply Or.inl
      intro assump_13
      apply True.intro
    let assump_12 := assump_3 assump_17
    apply False.elim assump_12


variable (p2 p4 p6 p7 p0 p1 p5 : Prop)
theorem file59_40929 : (((((p6 ∨ p4) → (p1 → p1)) ∨ ((p2 ∧ p0) → (p4 ∨ p1))) → False) → ((((p2 ∨ p5) ∧ (True → False)) ∨ ((True ∨ p5) ∧ (p4 ∨ False))) ∨ (((p7 ∨ p7) → (p1 ∧ p4)) → ((p0 → p5) ∧ (p0 → p1))))) := by
  intro assump_1
  apply Or.inr
  intro assump_4
  apply And.intro
  intro assump_5
  have assump_47 : (((p6 ∨ p4) → (p1 → p1)) ∨ ((p2 ∧ p0) → (p4 ∨ p1))) := by
    apply Or.inl
    intro assump_13
    intro assump_14
    cases assump_13
    case inl assump_17 =>
      exact assump_14
    case inr assump_18 =>
      exact assump_14
  let assump_12 := assump_1 assump_47
  apply False.elim assump_12
  intro assump_26
  have assump_48 : (((p6 ∨ p4) → (p1 → p1)) ∨ ((p2 ∧ p0) → (p4 ∨ p1))) := by
    apply Or.inl
    intro assump_34
    intro assump_35
    cases assump_34
    case inl assump_38 =>
      exact assump_35
    case inr assump_39 =>
      exact assump_35
  let assump_33 := assump_1 assump_48
  apply False.elim assump_33


variable (p1 p3 p6 p0 p4 : Prop)
theorem file59_41912 : (((((p4 ∧ p1) → False) ∧ ((p4 → False) → (p4 ∨ p6))) ∧ (((True → False) → False) → False)) → ((((p6 → p3) → False) → ((p6 ∨ p6) ∧ (p0 → True))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      have assump_26 : ((True → False) → False) := by
        intro assump_16
        have assump_27 : True := by
          apply True.intro
        let assump_19 := assump_16 assump_27
        apply False.elim assump_19
      let assump_15 := assump_6 assump_26
      apply False.elim assump_15


variable (p5 p4 p2 p1 p0 p3 p6 : Prop)
theorem file59_42571 : (((((True ∧ p2) → (False ∧ p6)) → ((p2 ∨ False) → (p0 → p1))) ∨ (((p0 → False) ∧ (p5 ∨ p1)) ∨ ((True → False) ∧ (p1 ∧ p4)))) ∨ ((((p2 → p2) → (False → False)) → False) → (((p0 ∨ p1) ∨ (p3 → p2)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_6
  case inl assump_10 =>
    have assump_23 : (True ∧ p2) := by
      apply And.intro
      apply True.intro
      exact assump_10
    let assump_16 := assump_5 assump_23
    let assump_17 := And.left assump_16
    apply False.elim assump_17
  case inr assump_11 =>
    apply False.elim assump_11


variable (p7 : Prop)
theorem file59_43222 : (((((p7 ∨ p7) ∧ (True → False)) → ((False → False) → False)) → False) → False) := by
  intro assump_1
  have assump_32 : (((p7 ∨ p7) ∧ (True → False)) → ((False → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        have assump_33 : True := by
          apply True.intro
        let assump_17 := assump_10 assump_33
        apply False.elim assump_17
      case inr assump_12 =>
        have assump_34 : True := by
          apply True.intro
        let assump_25 := assump_10 assump_34
        apply False.elim assump_25
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p4 p0 p6 p7 p3 p5 p1 p2 : Prop)
theorem file59_43996 : (((((p0 ∧ p3) → (p4 ∨ p6)) → ((p2 ∨ p4) ∨ (False → False))) ∨ (((p7 → p3) ∨ (p3 ∨ p5)) → ((p7 ∧ p0) ∨ (True ∧ p5)))) ∨ ((((p0 → False) ∧ (p2 → p3)) → False) ∧ (((p2 ∨ p2) → (p1 → p5)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  apply False.elim assump_4


variable (p0 p2 p5 p1 p6 p3 p4 : Prop)
theorem file59_44367 : ((((((False → False) ∨ (p4 → p5)) ∨ ((p5 → p4) → (False → p1))) ∧ (((p5 ∧ p0) → (p4 → False)) ∧ ((True → True) → False))) ∨ ((((p5 ∧ p5) ∨ (p1 ∧ p6)) ∨ ((False → p2) ∨ (p3 ∨ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case intro assump_12 assump_13 =>
            have assump_58 : (True → True) := by
              intro assump_19
              apply True.intro
            let assump_18 := assump_13 assump_58
            apply False.elim assump_18
        case inr assump_9 =>
          cases assump_5
          case intro assump_25 assump_26 =>
            have assump_59 : (True → True) := by
              intro assump_32
              apply True.intro
            let assump_31 := assump_26 assump_59
            apply False.elim assump_31
      case inr assump_7 =>
        cases assump_5
        case intro assump_38 assump_39 =>
          have assump_60 : (True → True) := by
            intro assump_45
            apply True.intro
          let assump_44 := assump_39 assump_60
          apply False.elim assump_44
  case inr assump_3 =>
    have assump_61 : (((p5 ∧ p5) ∨ (p1 ∧ p6)) ∨ ((False → p2) ∨ (p3 ∨ p0))) := by
      apply Or.inr
      apply Or.inl
      intro assump_52
      apply False.elim assump_52
    let assump_51 := assump_3 assump_61
    apply False.elim assump_51


variable (p5 p2 p3 p4 p1 : Prop)
theorem file59_45953 : (((((p5 → p5) → False) → ((p3 → True) → (p1 → True))) → False) → ((((p1 → False) ∨ (p4 ∨ p5)) → False) → (((p3 → p3) ∧ (p2 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    have assump_21 : (((p5 → p5) → False) → ((p3 → True) → (p1 → True))) := by
      intro assump_15
      intro assump_16
      intro assump_17
      apply True.intro
    let assump_14 := assump_1 assump_21
    apply False.elim assump_14


variable (p1 p6 p2 p4 p5 p7 p0 : Prop)
theorem file59_46507 : (((((p1 ∧ p1) → False) → ((p2 → True) ∨ (p7 → False))) → False) → ((((p1 ∨ True) → (p2 → p4)) → False) ∧ (((p6 → False) ∨ (p0 → False)) ∨ ((p5 → False) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  have assump_29 : (((p1 ∧ p1) → False) → ((p2 → True) ∨ (p7 → False))) := by
    intro assump_8
    apply Or.inl
    intro assump_11
    apply True.intro
  let assump_7 := assump_1 assump_29
  apply False.elim assump_7
  apply Or.inl
  apply Or.inl
  intro assump_17
  have assump_30 : (((p1 ∧ p1) → False) → ((p2 → True) ∨ (p7 → False))) := by
    intro assump_22
    apply Or.inl
    intro assump_25
    apply True.intro
  let assump_21 := assump_1 assump_30
  apply False.elim assump_21


variable (p4 p2 p5 p7 p6 p0 p3 : Prop)
theorem file59_47283 : (((((p4 ∧ p5) ∨ (p2 → False)) → False) → (((p6 ∧ p7) → (p0 → False)) → ((p7 ∧ p5) → (p0 → p5)))) ∨ ((((p0 ∨ p4) → False) → ((p6 → p6) ∨ (True → False))) ∧ (((p6 ∨ p5) → (True → False)) ∨ ((p2 → False) ∨ (p3 → p7))))) := by
  apply Or.inl
  intro assump_10
  intro assump_11
  intro assump_12
  intro assump_13
  cases assump_12
  case intro assump_16 assump_17 =>
    exact assump_17


variable (p7 p0 p2 p6 p3 p4 p5 : Prop)
theorem file59_47730 : (((((p4 → False) ∨ (True → False)) → ((p0 ∨ p5) → False)) → False) → ((((p6 → p6) ∨ (True → p5)) ∧ ((p5 → p0) → (p6 ∨ p2))) → (((p7 ∨ p7) ∧ (p6 ∧ p3)) ∨ ((False ∧ p5) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      apply Or.inr
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
    case inr assump_6 =>
      apply Or.inr
      intro assump_24
      cases assump_24
      case intro assump_25 assump_26 =>
        apply False.elim assump_25


variable (p3 p6 p2 p7 p1 p5 p0 p4 : Prop)
theorem file59_48411 : (((((p3 → False) ∨ (True → False)) → False) ∧ (((False → False) → False) ∧ ((p7 ∨ p6) ∧ (p7 → p0)))) → ((((p5 ∧ p4) ∧ (p5 ∨ p3)) → False) ∨ (((p3 ∧ p1) → (p5 → False)) ∨ ((p4 → False) ∨ (p2 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          apply Or.inl
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_20
              case inl assump_27 =>
                have assump_102 : (False → False) := by
                  intro assump_38
                  apply False.elim assump_38
                let assump_37 := assump_6 assump_102
                apply False.elim assump_37
              case inr assump_28 =>
                have assump_103 : (False → False) := by
                  intro assump_53
                  apply False.elim assump_53
                let assump_52 := assump_6 assump_103
                apply False.elim assump_52
        case inr assump_13 =>
          apply Or.inl
          intro assump_63
          cases assump_63
          case intro assump_64 assump_65 =>
            cases assump_64
            case intro assump_66 assump_67 =>
              cases assump_65
              case inl assump_72 =>
                have assump_104 : (False → False) := by
                  intro assump_82
                  apply False.elim assump_82
                let assump_81 := assump_6 assump_104
                apply False.elim assump_81
              case inr assump_73 =>
                have assump_105 : (False → False) := by
                  intro assump_96
                  apply False.elim assump_96
                let assump_95 := assump_6 assump_105
                apply False.elim assump_95


variable (p1 p2 p0 p6 p5 p4 p7 : Prop)
theorem file59_50465 : (((((p0 → False) ∨ (p2 → p4)) ∧ ((False → p1) → False)) ∨ (((p4 → True) ∨ (False → False)) → False)) → ((((p1 → False) ∧ (p7 ∧ p1)) → False) ∨ (((p7 → p5) ∧ (False ∧ p7)) → ((p6 ∨ p0) → (False ∨ p5))))) := by
  intro assump_23
  cases assump_23
  case inl assump_24 =>
    cases assump_24
    case intro assump_26 assump_27 =>
      cases assump_26
      case inl assump_28 =>
        apply Or.inl
        intro assump_34
        cases assump_34
        case intro assump_35 assump_36 =>
          cases assump_36
          case intro assump_39 assump_40 =>
            have assump_91 : p1 := by
              exact assump_40
            let assump_47 := assump_35 assump_91
            apply False.elim assump_47
      case inr assump_29 =>
        apply Or.inl
        intro assump_55
        cases assump_55
        case intro assump_56 assump_57 =>
          cases assump_57
          case intro assump_60 assump_61 =>
            have assump_92 : p1 := by
              exact assump_61
            let assump_68 := assump_56 assump_92
            apply False.elim assump_68
  case inr assump_25 =>
    apply Or.inl
    intro assump_74
    cases assump_74
    case intro assump_75 assump_76 =>
      cases assump_76
      case intro assump_79 assump_80 =>
        have assump_93 : p1 := by
          exact assump_80
        let assump_87 := assump_75 assump_93
        apply False.elim assump_87


variable (p1 p0 p2 : Prop)
theorem file59_51916 : ((((((False ∧ p0) → (p1 ∧ p2)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_24 : ((((False ∧ p0) → (p1 ∧ p2)) → False) → False) := by
    intro assump_5
    have assump_25 : ((False ∧ p0) → (p1 ∧ p2)) := by
      intro assump_9
      apply And.intro
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
      cases assump_9
      case intro assump_14 assump_15 =>
        apply False.elim assump_14
    let assump_8 := assump_5 assump_25
    apply False.elim assump_8
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p6 p2 p5 p1 p7 p3 p0 : Prop)
theorem file59_52583 : (((((p3 ∨ p0) ∧ (p0 → False)) → ((p6 ∨ p3) → False)) → (((True → False) → False) ∧ ((p3 ∨ True) ∨ (p7 → p1)))) ∨ ((((p5 → False) ∧ (p6 → False)) ∨ ((p6 ∧ p2) → False)) → False)) := by
  apply Or.inl
  intro assump_29
  apply And.intro
  intro assump_30
  have assump_42 : True := by
    apply True.intro
  let assump_36 := assump_30 assump_42
  apply False.elim assump_36
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p4 p0 p5 p1 : Prop)
theorem file59_53058 : (((((p0 → False) → (False → False)) → False) ∧ (((p1 → p1) ∨ (True → p0)) → ((p1 → p1) → False))) → ((((p4 → False) → False) → False) ∧ (((False ∧ p0) ∧ (False → p5)) ∧ ((False → False) ∨ (p1 → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_68 : ((p1 → p1) ∨ (True → p0)) := by
      apply Or.inl
      intro assump_12
      exact assump_12
    let assump_11 := assump_6 assump_68
    have assump_69 : (p1 → p1) := by
      intro assump_16
      exact assump_16
    let assump_15 := assump_11 assump_69
    apply False.elim assump_15
  apply And.intro
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_22 assump_23 =>
    have assump_70 : ((p1 → p1) ∨ (True → p0)) := by
      apply Or.inl
      intro assump_29
      exact assump_29
    let assump_28 := assump_23 assump_70
    have assump_71 : (p1 → p1) := by
      intro assump_33
      exact assump_33
    let assump_32 := assump_28 assump_71
    apply False.elim assump_32
  cases assump_1
  case intro assump_39 assump_40 =>
    have assump_72 : ((p1 → p1) ∨ (True → p0)) := by
      apply Or.inl
      intro assump_46
      exact assump_46
    let assump_45 := assump_40 assump_72
    have assump_73 : (p1 → p1) := by
      intro assump_50
      exact assump_50
    let assump_49 := assump_45 assump_73
    apply False.elim assump_49
  intro assump_56
  apply False.elim assump_56
  cases assump_1
  case intro assump_59 assump_60 =>
    apply Or.inl
    intro assump_65
    apply False.elim assump_65


variable (p5 p1 p3 p4 p7 : Prop)
theorem file59_54686 : (((((False ∧ p3) ∧ (p5 ∨ p1)) → False) → False) → ((((p7 → False) ∧ (p4 → False)) → False) ∧ (((p7 → True) → False) ∧ ((False ∨ True) ∧ (p7 ∨ p7))))) := by
  intro assump_28
  apply And.intro
  intro assump_29
  cases assump_29
  case intro assump_30 assump_31 =>
    have assump_80 : (((False ∧ p3) ∧ (p5 ∨ p1)) → False) := by
      intro assump_39
      cases assump_39
      case intro assump_40 assump_41 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          apply False.elim assump_42
    let assump_38 := assump_28 assump_80
    apply False.elim assump_38
  apply And.intro
  intro assump_49
  have assump_81 : (((False ∧ p3) ∧ (p5 ∨ p1)) → False) := by
    intro assump_55
    cases assump_55
    case intro assump_56 assump_57 =>
      cases assump_56
      case intro assump_58 assump_59 =>
        apply False.elim assump_58
  let assump_54 := assump_28 assump_81
  apply False.elim assump_54
  apply And.intro
  apply Or.inr
  apply True.intro
  have assump_82 : (((False ∧ p3) ∧ (p5 ∨ p1)) → False) := by
    intro assump_70
    cases assump_70
    case intro assump_71 assump_72 =>
      cases assump_71
      case intro assump_73 assump_74 =>
        apply False.elim assump_73
  let assump_69 := assump_28 assump_82
  apply False.elim assump_69


variable (p6 p3 p2 p5 p4 p7 : Prop)
theorem file59_56031 : ((((((p6 ∧ p7) → False) → ((True ∨ p3) → (p7 → False))) → (((p3 → False) → False) ∨ ((p3 → p2) ∨ (p4 → False)))) ∧ ((((p7 → p5) → False) → ((p4 ∨ False) ∨ (p5 → p5))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((p7 → p5) → False) → ((p4 ∨ False) ∨ (p5 → p5))) := by
      intro assump_9
      apply Or.inr
      intro assump_12
      exact assump_12
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p7 p4 p1 p0 p5 p3 p2 : Prop)
theorem file59_56585 : ((((((p3 → False) ∨ (p3 → p2)) → ((False ∨ p1) → False)) → (((False ∧ p4) → False) → ((False → p1) → (p4 → False)))) ∧ ((((True → False) ∧ (p0 ∨ p5)) → ((p7 → True) → (p2 ∧ p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_58 : (((True → False) ∧ (p0 ∨ p5)) → ((p7 → True) → (p2 ∧ p4))) := by
      intro assump_9
      intro assump_10
      apply And.intro
      cases assump_9
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          have assump_59 : True := by
            apply True.intro
          let assump_22 := assump_13 assump_59
          apply False.elim assump_22
        case inr assump_18 =>
          have assump_60 : True := by
            apply True.intro
          let assump_29 := assump_13 assump_60
          apply False.elim assump_29
      cases assump_9
      case intro assump_35 assump_36 =>
        cases assump_36
        case inl assump_39 =>
          have assump_61 : True := by
            apply True.intro
          let assump_44 := assump_35 assump_61
          apply False.elim assump_44
        case inr assump_40 =>
          have assump_62 : True := by
            apply True.intro
          let assump_51 := assump_35 assump_62
          apply False.elim assump_51
    let assump_8 := assump_3 assump_58
    apply False.elim assump_8


variable (p2 p0 p5 p7 p3 p6 p4 : Prop)
theorem file59_58034 : ((((((p3 → False) ∧ (p5 ∧ p0)) ∧ ((False → p4) → (p2 ∧ False))) → (((p4 → p3) ∨ (p6 ∨ p5)) ∧ ((p5 → p4) → (p5 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_78 : ((((p3 → False) ∧ (p5 ∧ p0)) ∧ ((False → p4) → (p2 ∧ False))) → (((p4 → p3) ∨ (p6 ∨ p5)) ∧ ((p5 → p4) → (p5 ∧ p7)))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_20
          have assump_79 : (False → p4) := by
            intro assump_25
            apply False.elim assump_25
          let assump_24 := assump_7 assump_79
          let assump_28 := And.right assump_24
          apply False.elim assump_28
    intro assump_33
    apply And.intro
    cases assump_5
    case intro assump_36 assump_37 =>
      cases assump_36
      case intro assump_38 assump_39 =>
        cases assump_39
        case intro assump_42 assump_43 =>
          exact assump_42
    cases assump_5
    case intro assump_52 assump_53 =>
      cases assump_52
      case intro assump_54 assump_55 =>
        cases assump_55
        case intro assump_58 assump_59 =>
          have assump_80 : (False → p4) := by
            intro assump_67
            apply False.elim assump_67
          let assump_66 := assump_53 assump_80
          let assump_70 := And.right assump_66
          apply False.elim assump_70
  let assump_4 := assump_1 assump_78
  apply False.elim assump_4


variable (p2 p1 p7 p4 p6 p0 : Prop)
theorem file59_59651 : (((((p6 → False) ∧ (True ∧ p6)) → False) → (((p7 → p1) ∨ (p2 ∨ True)) → ((False → False) ∨ (p7 ∧ p1)))) ∨ ((((True ∨ True) ∨ (False ∧ p0)) ∨ ((False ∧ p4) → (p4 → p7))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    apply False.elim assump_9
  case inr assump_4 =>
    cases assump_4
    case inl assump_12 =>
      apply Or.inl
      intro assump_18
      apply False.elim assump_18
    case inr assump_13 =>
      apply Or.inl
      intro assump_25
      apply False.elim assump_25


variable (p1 : Prop)
theorem file59_60278 : ((((((True ∨ p1) ∨ (p1 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ p1) ∨ (p1 → False)) → False) → False) := by
    intro assump_5
    have assump_16 : ((True ∨ p1) ∨ (p1 → False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p1 p6 p3 p5 p2 p4 p0 : Prop)
theorem file59_60780 : (((((p0 ∧ True) ∧ (p5 ∧ p6)) ∧ ((p4 ∧ False) → (p3 → p7))) → (((p1 → p1) ∨ (p3 → p6)) → ((p4 ∧ p5) ∨ (p6 → p0)))) → ((((p5 ∧ p5) → False) ∨ ((p2 → False) ∨ (p0 → False))) → (((True ∨ p7) ∨ (p5 → False)) ∨ ((p4 ∨ True) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_4 =>
    cases assump_4
    case inl assump_9 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_10 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p2 p6 : Prop)
theorem file59_61463 : (((((p6 → False) ∧ (True → p2)) → ((False → p2) ∨ (p2 → False))) → False) → False) := by
  intro assump_14
  have assump_31 : (((p6 → False) ∧ (True → p2)) → ((False → p2) ∨ (p2 → False))) := by
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      apply Or.inl
      intro assump_25
      apply False.elim assump_25
  let assump_17 := assump_14 assump_31
  apply False.elim assump_17


variable (p3 p0 p1 p7 p4 : Prop)
theorem file59_61935 : (((((p4 ∧ p1) ∨ (p1 → False)) ∧ ((p7 ∧ False) → False)) → False) → ((((p0 ∧ p0) → False) → False) → (((p7 → False) ∨ (p3 → False)) → ((p0 ∧ True) ∨ (False → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    apply Or.inr
    intro assump_12
    apply False.elim assump_12
  case inr assump_5 =>
    apply Or.inr
    intro assump_21
    apply False.elim assump_21


variable (p6 p7 p2 p1 p3 p0 p5 p4 : Prop)
theorem file59_62425 : (((((p3 → p7) → False) ∧ ((p7 → p4) ∧ (p3 ∨ p0))) ∨ (((p0 ∨ p2) ∨ (p6 ∧ p1)) → ((p0 → p4) ∧ (p3 → False)))) → ((((p7 ∨ p2) → (False ∧ p2)) → False) → (((False ∧ p4) ∨ (p1 ∨ p2)) ∨ ((p5 ∧ p7) ∨ (True ∨ p5))))) := by
  intro assump_14
  intro assump_15
  cases assump_14
  case inl assump_18 =>
    cases assump_18
    case intro assump_20 assump_21 =>
      cases assump_21
      case intro assump_24 assump_25 =>
        cases assump_25
        case inl assump_28 =>
          apply Or.inr
          apply Or.inr
          apply Or.inl
          apply True.intro
        case inr assump_29 =>
          apply Or.inr
          apply Or.inr
          apply Or.inl
          apply True.intro
  case inr assump_19 =>
    apply Or.inr
    apply Or.inr
    apply Or.inl
    apply True.intro


variable (p0 p2 p6 p4 p5 p1 p3 : Prop)
theorem file59_63273 : (((((p6 ∧ p2) ∨ (p4 → False)) ∧ ((p3 ∨ p2) ∨ (True ∧ p2))) → (((p1 → p2) ∧ (p6 → False)) → ((True → False) → False))) ∨ ((((p4 ∧ p1) → (True → False)) ∨ ((p0 ∨ p6) → False)) ∧ (((p2 → False) → False) → ((p5 ∨ True) ∨ (p0 ∧ False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_13
          case inl assump_22 =>
            cases assump_22
            case inl assump_24 =>
              have assump_97 : p6 := by
                exact assump_16
              let assump_31 := assump_7 assump_97
              apply False.elim assump_31
            case inr assump_25 =>
              have assump_98 : p6 := by
                exact assump_16
              let assump_40 := assump_7 assump_98
              apply False.elim assump_40
          case inr assump_23 =>
            cases assump_23
            case intro assump_44 assump_45 =>
              have assump_99 : p6 := by
                exact assump_16
              let assump_53 := assump_7 assump_99
              apply False.elim assump_53
      case inr assump_15 =>
        cases assump_13
        case inl assump_59 =>
          cases assump_59
          case inl assump_61 =>
            have assump_100 : True := by
              apply True.intro
            let assump_69 := assump_3 assump_100
            apply False.elim assump_69
          case inr assump_62 =>
            have assump_101 : True := by
              apply True.intro
            let assump_79 := assump_3 assump_101
            apply False.elim assump_79
        case inr assump_60 =>
          cases assump_60
          case intro assump_83 assump_84 =>
            have assump_102 : True := by
              apply True.intro
            let assump_93 := assump_3 assump_102
            apply False.elim assump_93


variable (p7 p0 p1 p6 : Prop)
theorem file59_65358 : ((((((p6 → p6) → False) ∧ ((p1 → p0) ∨ (p7 ∧ False))) → False) → False) → False) := by
  intro assump_6
  have assump_36 : ((((p6 → p6) → False) ∧ ((p1 → p0) ∨ (p7 ∧ False))) → False) := by
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      cases assump_12
      case inl assump_15 =>
        have assump_37 : (p6 → p6) := by
          intro assump_21
          exact assump_21
        let assump_20 := assump_11 assump_37
        apply False.elim assump_20
      case inr assump_16 =>
        cases assump_16
        case intro assump_27 assump_28 =>
          apply False.elim assump_28
  let assump_9 := assump_6 assump_36
  apply False.elim assump_9


variable (p6 p2 p4 p5 p0 p1 : Prop)
theorem file59_66105 : (((((p1 ∨ p6) → (p4 → False)) → ((p5 ∨ p4) ∨ (p6 → False))) → (((p0 ∨ True) ∧ (p5 → p0)) ∧ ((p2 ∨ p5) → False))) → ((((True ∨ p1) ∧ (False → False)) ∨ ((p2 → False) ∨ (p4 → True))) ∧ (((p2 ∧ False) ∧ (p4 → p0)) → ((True ∨ p6) ∧ (p2 → p4))))) := by
  intro assump_5
  apply And.intro
  apply Or.inl
  apply And.intro
  apply Or.inl
  apply True.intro
  intro assump_8
  apply False.elim assump_8
  intro assump_11
  apply And.intro
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case intro assump_14 assump_15 =>
      apply False.elim assump_15
  intro assump_20
  cases assump_11
  case intro assump_23 assump_24 =>
    cases assump_23
    case intro assump_25 assump_26 =>
      apply False.elim assump_26


variable (p4 p6 p0 p7 : Prop)
theorem file59_66898 : (((((p0 → False) → (True ∨ p7)) → False) → (((True ∧ True) → False) ∧ ((p4 ∧ p7) → False))) ∨ ((((p6 → False) → False) ∨ ((True → p6) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_34 : ((p0 → False) → (True ∨ p7)) := by
      intro assump_12
      apply Or.inl
      apply True.intro
    let assump_11 := assump_1 assump_34
    apply False.elim assump_11
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    have assump_35 : ((p0 → False) → (True ∨ p7)) := by
      intro assump_28
      apply Or.inl
      apply True.intro
    let assump_27 := assump_1 assump_35
    apply False.elim assump_27


variable (p5 p2 p4 p1 p0 p3 : Prop)
theorem file59_67690 : (((((False ∧ False) → (True → p4)) ∨ ((p0 ∨ False) ∧ (p2 ∧ p0))) → False) → ((((p5 ∨ p2) → (p2 → False)) ∨ ((p0 ∨ p3) → False)) ∧ (((p2 → False) ∧ (p1 ∨ p2)) → False))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    have assump_81 : (((False ∧ False) → (True → p4)) ∨ ((p0 ∨ False) ∧ (p2 ∧ p0))) := by
      apply Or.inl
      intro assump_15
      intro assump_16
      cases assump_15
      case intro assump_19 assump_20 =>
        apply False.elim assump_19
    let assump_14 := assump_1 assump_81
    apply False.elim assump_14
  case inr assump_9 =>
    have assump_82 : (((False ∧ False) → (True → p4)) ∨ ((p0 ∨ False) ∧ (p2 ∧ p0))) := by
      apply Or.inl
      intro assump_31
      intro assump_32
      cases assump_31
      case intro assump_35 assump_36 =>
        apply False.elim assump_35
    let assump_30 := assump_1 assump_82
    apply False.elim assump_30
  intro assump_42
  cases assump_42
  case intro assump_43 assump_44 =>
    cases assump_44
    case inl assump_47 =>
      have assump_83 : (((False ∧ False) → (True → p4)) ∨ ((p0 ∨ False) ∧ (p2 ∧ p0))) := by
        apply Or.inl
        intro assump_54
        intro assump_55
        cases assump_54
        case intro assump_58 assump_59 =>
          apply False.elim assump_58
      let assump_53 := assump_1 assump_83
      apply False.elim assump_53
    case inr assump_48 =>
      have assump_84 : (((False ∧ False) → (True → p4)) ∨ ((p0 ∨ False) ∧ (p2 ∧ p0))) := by
        apply Or.inl
        intro assump_70
        intro assump_71
        cases assump_70
        case intro assump_74 assump_75 =>
          apply False.elim assump_74
      let assump_69 := assump_1 assump_84
      apply False.elim assump_69


variable (p7 p4 p0 p5 p1 p3 p6 : Prop)
theorem file59_69539 : (((((p4 → True) ∧ (True → False)) → False) ∧ (((p7 ∨ p0) → False) → ((False → False) ∨ (p5 ∧ p7)))) → ((((True ∧ p0) ∧ (p1 → False)) → ((p7 → False) ∧ (p6 ∧ p5))) → (((p7 → p5) ∧ (p1 ∨ True)) → ((True ∧ p3) ∨ (False → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_5
    case inl assump_8 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        apply Or.inr
        intro assump_20
        apply False.elim assump_20
    case inr assump_9 =>
      cases assump_1
      case intro assump_27 assump_28 =>
        apply Or.inr
        intro assump_33
        apply False.elim assump_33


variable (p2 p0 p6 p3 p5 p1 p7 : Prop)
theorem file59_70290 : ((((((p5 ∧ False) ∨ (p7 → False)) → ((True → False) → False)) ∨ (((p2 ∨ p6) ∧ (p5 ∨ p7)) ∨ ((True ∨ False) → (p3 ∨ True)))) → ((((p1 ∧ True) ∧ (False ∧ p0)) ∧ ((p5 ∧ True) ∨ (p5 → False))) ∧ (((p7 ∧ p6) ∧ (p0 ∨ False)) → False))) → False) := by
  intro assump_1
  have assump_34 : ((((p5 ∧ False) ∨ (p7 → False)) → ((True → False) → False)) ∨ (((p2 ∨ p6) ∧ (p5 ∨ p7)) ∨ ((True ∨ False) → (p3 ∨ True)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
    case inr assump_10 =>
      have assump_35 : True := by
        apply True.intro
      let assump_20 := assump_6 assump_35
      apply False.elim assump_20
  let assump_4 := assump_1 assump_34
  let assump_24 := And.left assump_4
  let assump_25 := And.left assump_24
  let assump_26 := And.right assump_25
  let assump_30 := And.left assump_26
  apply False.elim assump_30


variable (p0 p7 p1 p4 p3 p6 p5 p2 : Prop)
theorem file59_71338 : ((((((p7 ∧ p2) → (p1 → True)) → False) ∧ (((p5 → p1) → False) → False)) ∧ ((((p2 ∧ p4) ∨ (p2 → p0)) ∧ ((False ∨ False) ∧ (p3 ∨ p2))) ∧ (((p1 → p2) → False) ∧ ((p3 ∨ p6) → False)))) → False) := by
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
          case inl assump_14 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_13
              case intro assump_22 assump_23 =>
                cases assump_22
                case inl assump_24 =>
                  apply False.elim assump_24
                case inr assump_25 =>
                  apply False.elim assump_25
          case inr assump_15 =>
            cases assump_13
            case intro assump_32 assump_33 =>
              cases assump_32
              case inl assump_34 =>
                apply False.elim assump_34
              case inr assump_35 =>
                apply False.elim assump_35


variable (p1 p4 p6 p2 p0 p7 p3 p5 : Prop)
theorem file59_72552 : (((((p2 ∨ p5) → False) → ((p6 → False) ∧ (p2 → False))) ∧ (((p3 → p3) → (p7 → p4)) ∧ ((p0 ∨ p0) → (p5 ∧ False)))) → ((((p7 → p0) → (p6 → True)) ∧ ((True ∨ p1) ∨ (p1 ∧ False))) ∨ (((p0 ∧ p2) → False) → ((p3 ∨ p1) ∨ (p5 ∧ p1))))) := by
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_15
    case intro assump_18 assump_19 =>
      apply Or.inl
      apply And.intro
      intro assump_24
      intro assump_25
      apply True.intro
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p7 p0 p5 p4 p3 p2 : Prop)
theorem file59_73145 : (((((p3 ∨ p5) → (False → False)) → False) → False) ∨ ((((p0 → p3) → False) → ((p2 ∧ p0) → (p7 ∨ p4))) → (((False → False) → False) → False))) := by
  apply Or.inl
  intro assump_30
  have assump_41 : ((p3 ∨ p5) → (False → False)) := by
    intro assump_34
    intro assump_35
    apply False.elim assump_35
  let assump_33 := assump_30 assump_41
  apply False.elim assump_33


variable (p7 p1 p5 p4 p0 p2 p3 : Prop)
theorem file59_73583 : (((((p5 ∨ p7) → False) ∧ ((True → p2) → False)) → False) → ((((p1 ∧ p1) ∨ (p5 → False)) → ((p3 ∨ p0) → (p2 → False))) → (((False → p3) ∨ (p4 → False)) ∨ ((p1 → False) → (p4 ∧ p7))))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  apply Or.inl
  intro assump_7
  apply False.elim assump_7


variable (p7 p6 p5 p0 p3 p1 p4 p2 : Prop)
theorem file59_73947 : ((((((p0 ∧ p0) → (p7 ∨ p0)) → ((False → p2) ∨ (p4 ∧ p1))) ∧ (((p6 ∧ p2) ∨ (p3 → False)) ∨ ((p4 ∧ p5) → False))) ∧ ((((p4 ∧ p1) ∨ (True ∧ p2)) → ((p5 → p5) → (p5 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            have assump_49 : (((p4 ∧ p1) ∨ (True ∧ p2)) → ((p5 → p5) → (p5 → True))) := by
              intro assump_21
              intro assump_22
              intro assump_23
              apply True.intro
            let assump_20 := assump_3 assump_49
            apply False.elim assump_20
        case inr assump_11 =>
          have assump_50 : (((p4 ∧ p1) ∨ (True ∧ p2)) → ((p5 → p5) → (p5 → True))) := by
            intro assump_32
            intro assump_33
            intro assump_34
            apply True.intro
          let assump_31 := assump_3 assump_50
          apply False.elim assump_31
      case inr assump_9 =>
        have assump_51 : (((p4 ∧ p1) ∨ (True ∧ p2)) → ((p5 → p5) → (p5 → True))) := by
          intro assump_43
          intro assump_44
          intro assump_45
          apply True.intro
        let assump_42 := assump_3 assump_51
        apply False.elim assump_42


variable (p5 p0 p1 p4 p2 : Prop)
theorem file59_75406 : (((((p1 → p0) → (True ∨ p5)) → False) ∧ (((False → p2) ∧ (p1 ∧ p4)) ∧ ((True ∨ p5) ∧ (p1 → False)))) → False) := by
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
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              have assump_38 : p1 := by
                exact assump_12
              let assump_26 := assump_19 assump_38
              apply False.elim assump_26
            case inr assump_21 =>
              have assump_39 : p1 := by
                exact assump_12
              let assump_34 := assump_19 assump_39
              apply False.elim assump_34


variable (p1 p3 p0 : Prop)
theorem file59_76313 : ((((((p1 ∨ p1) → False) ∧ ((p3 ∨ p0) ∧ (False ∧ True))) → False) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p1 ∨ p1) → False) ∧ ((p3 ∨ p0) ∧ (False ∧ True))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_11
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
        case inr assump_13 =>
          cases assump_11
          case intro assump_22 assump_23 =>
            apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p7 p1 p2 p3 p6 p0 : Prop)
theorem file59_77069 : ((((((p6 → p6) ∨ (p3 ∨ p2)) → ((True ∧ False) → False)) ∨ (((p7 ∧ p0) ∧ (p3 → p0)) ∧ ((p1 ∧ p2) → (p1 ∧ p2)))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p6 → p6) ∨ (p3 ∨ p2)) → ((True ∧ False) → False)) ∨ (((p7 ∧ p0) ∧ (p3 → p0)) ∧ ((p1 ∧ p2) → (p1 ∧ p2)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p0 p2 p5 p3 p1 p4 : Prop)
theorem file59_77622 : (((((p3 ∧ p4) → (p4 ∨ False)) ∨ ((p5 → False) ∧ (p4 ∨ p3))) ∨ (((p1 → False) ∧ (False → False)) ∨ ((p1 → False) → (p1 ∨ p3)))) ∨ ((((True ∧ p0) → (p5 ∨ p4)) ∨ ((p5 ∧ p0) → (p2 ∨ p5))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    apply Or.inl
    exact assump_21


variable (p0 p1 p3 p4 : Prop)
theorem file59_78030 : (((((p3 ∧ False) ∧ (p0 ∨ p4)) → ((p4 → False) ∧ (p1 → False))) → False) → False) := by
  intro assump_1
  have assump_31 : (((p3 ∧ False) ∧ (p0 ∨ p4)) → ((p4 → False) ∧ (p1 → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
    intro assump_17
    cases assump_5
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        apply False.elim assump_23
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p7 p6 p4 p3 p1 p5 p2 : Prop)
theorem file59_78732 : ((((((p6 ∧ p1) ∧ (p2 ∧ False)) ∧ ((True ∧ p5) ∧ (p5 → p5))) → (((p1 → p7) → (p7 → False)) ∨ ((p4 ∨ False) ∨ (p3 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p6 ∧ p1) ∧ (p2 ∧ False)) ∧ ((True ∧ p5) ∧ (p5 → p5))) → (((p1 → p7) → (p7 → False)) ∨ ((p4 ∨ False) ∨ (p3 ∨ False)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p6 p2 p7 p3 p0 p4 p5 : Prop)
theorem file59_79478 : (((((p6 ∧ False) ∨ (p4 ∧ p7)) ∨ ((p3 ∨ p4) ∨ (False ∧ False))) → (((p4 → True) ∧ (p5 → p2)) → False)) → ((((p5 ∨ p6) → (True → p2)) → False) → (((p2 → False) → False) → ((False ∧ p2) → (p0 → p2))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p7 p2 p5 : Prop)
theorem file59_79900 : ((((((p2 → False) ∧ (False ∨ True)) ∨ ((p7 ∨ p7) → False)) → (((False → False) → (p5 ∧ True)) → ((True → False) → (False ∧ True)))) → False) → False) := by
  intro assump_1
  have assump_53 : ((((p2 → False) ∧ (False ∨ True)) ∨ ((p7 ∨ p7) → False)) → (((False → False) → (p5 ∧ True)) → ((True → False) → (False ∧ True)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply And.intro
    cases assump_5
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_15
        case inl assump_18 =>
          apply False.elim assump_18
        case inr assump_19 =>
          have assump_54 : True := by
            apply True.intro
          let assump_32 := assump_7 assump_54
          apply False.elim assump_32
    case inr assump_13 =>
      have assump_55 : True := by
        apply True.intro
      let assump_46 := assump_7 assump_55
      apply False.elim assump_46
    apply True.intro
  let assump_4 := assump_1 assump_53
  apply False.elim assump_4


variable (p2 p6 p3 p0 p7 p1 p4 : Prop)
theorem file59_80992 : ((((((p2 → p6) ∧ (p4 → p0)) → ((p7 → False) → (p0 → False))) → (((False → p1) → (p7 ∧ p2)) ∧ ((True → p0) → (False → False)))) ∧ ((((False → p3) ∨ (p7 → False)) ∨ ((p3 → p0) ∧ (p1 ∧ p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((False → p3) ∨ (p7 → False)) ∨ ((p3 → p0) ∧ (p1 ∧ p7))) := by
      apply Or.inl
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p7 p3 p0 p2 p1 p4 : Prop)
theorem file59_81578 : ((((((p0 ∧ p2) → (True ∨ p3)) → ((True ∧ p4) → (True ∨ p0))) ∨ (((p7 → False) ∧ (p1 → False)) ∧ ((p7 ∧ p7) ∨ (p0 → p7)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p0 ∧ p2) → (True ∨ p3)) → ((True ∧ p4) → (True ∨ p0))) ∨ (((p7 → False) ∧ (p1 → False)) ∧ ((p7 ∧ p7) ∨ (p0 → p7)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p0 p6 p1 : Prop)
theorem file59_82154 : (((((True ∨ p6) ∨ (True → False)) ∨ ((p1 → p6) ∧ (p0 → False))) → False) → False) := by
  intro assump_1
  have assump_8 : (((True ∨ p6) ∨ (True → False)) ∨ ((p1 → p6) ∧ (p0 → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p0 p3 p4 p5 p6 : Prop)
theorem file59_82538 : (((((False ∧ p3) → False) → False) → False) ∧ ((((p3 → False) ∨ (True → p0)) → ((p5 ∧ p3) → (p5 ∧ True))) ∨ (((p4 → False) ∨ (True → False)) → ((p4 → p3) → (False → p6))))) := by
  apply And.intro
  intro assump_1
  have assump_27 : ((False ∧ p3) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4
  apply Or.inl
  intro assump_13
  intro assump_14
  apply And.intro
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_13
    case inl assump_21 =>
      exact assump_15
    case inr assump_22 =>
      exact assump_15
  apply True.intro


variable (p7 p4 p0 : Prop)
theorem file59_83280 : (((((False ∨ p0) → (p7 → True)) ∨ ((p4 ∨ True) ∧ (False ∨ False))) → (((True → False) → False) → False)) → False) := by
  intro assump_14
  have assump_31 : (((False ∨ p0) → (p7 → True)) ∨ ((p4 ∨ True) ∧ (False ∨ False))) := by
    apply Or.inl
    intro assump_18
    intro assump_19
    apply True.intro
  let assump_17 := assump_14 assump_31
  have assump_32 : ((True → False) → False) := by
    intro assump_21
    have assump_33 : True := by
      apply True.intro
    let assump_24 := assump_21 assump_33
    apply False.elim assump_24
  let assump_20 := assump_17 assump_32
  apply False.elim assump_20


variable (p0 p2 p4 p1 p7 p5 : Prop)
theorem file59_83950 : ((((((True ∨ p0) ∧ (p1 → p5)) → ((False → p7) ∨ (p4 → False))) → False) ∧ ((((p2 ∧ p7) → (p2 ∨ False)) ∨ ((p0 → False) → (p4 ∧ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : (((p2 ∧ p7) → (p2 ∨ False)) ∨ ((p0 → False) → (p4 ∧ p0))) := by
      apply Or.inl
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply Or.inl
        exact assump_10
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p7 p1 p3 p0 p4 p6 p2 : Prop)
theorem file59_84539 : (((((p1 → p3) → (p0 ∨ True)) → ((p7 → False) ∨ (p4 → False))) ∨ (((p2 ∨ p7) ∧ (p2 → p2)) → ((False ∧ p6) ∧ (p7 → True)))) → ((((p3 ∧ False) ∧ (p3 ∨ p0)) → False) ∨ (((p2 ∨ True) ∧ (False → False)) ∧ ((p3 → False) ∧ (p4 ∨ p7))))) := by
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


variable (p5 p6 p1 p3 p0 p7 : Prop)
theorem file59_85292 : (((((p7 ∧ p1) → (p1 → False)) ∨ ((p6 ∧ True) ∨ (False ∨ p0))) ∧ (((p5 ∨ True) ∨ (p5 ∧ True)) → False)) → ((((p3 → False) → False) ∨ ((True ∧ p6) → (p1 → False))) ∧ (((p1 → False) ∨ (p3 → p1)) ∧ ((p6 ∨ True) → (p3 → False))))) := by
  intro assump_20
  apply And.intro
  cases assump_20
  case intro assump_21 assump_22 =>
    cases assump_21
    case inl assump_23 =>
      apply Or.inl
      intro assump_29
      have assump_207 : ((p5 ∨ True) ∨ (p5 ∧ True)) := by
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_33 := assump_22 assump_207
      apply False.elim assump_33
    case inr assump_24 =>
      cases assump_24
      case inl assump_37 =>
        cases assump_37
        case intro assump_39 assump_40 =>
          apply Or.inl
          intro assump_47
          have assump_208 : ((p5 ∨ True) ∨ (p5 ∧ True)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_51 := assump_22 assump_208
          apply False.elim assump_51
      case inr assump_38 =>
        cases assump_38
        case inl assump_55 =>
          apply False.elim assump_55
        case inr assump_56 =>
          apply Or.inl
          intro assump_63
          have assump_209 : ((p5 ∨ True) ∨ (p5 ∧ True)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_67 := assump_22 assump_209
          apply False.elim assump_67
  apply And.intro
  cases assump_20
  case intro assump_71 assump_72 =>
    cases assump_71
    case inl assump_73 =>
      apply Or.inl
      intro assump_79
      have assump_210 : ((p5 ∨ True) ∨ (p5 ∧ True)) := by
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_83 := assump_72 assump_210
      apply False.elim assump_83
    case inr assump_74 =>
      cases assump_74
      case inl assump_87 =>
        cases assump_87
        case intro assump_89 assump_90 =>
          apply Or.inl
          intro assump_97
          have assump_211 : ((p5 ∨ True) ∨ (p5 ∧ True)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_101 := assump_72 assump_211
          apply False.elim assump_101
      case inr assump_88 =>
        cases assump_88
        case inl assump_105 =>
          apply False.elim assump_105
        case inr assump_106 =>
          apply Or.inl
          intro assump_113
          have assump_212 : ((p5 ∨ True) ∨ (p5 ∧ True)) := by
            apply Or.inl
            apply Or.inr
            apply True.intro
          let assump_117 := assump_72 assump_212
          apply False.elim assump_117
  intro assump_121
  intro assump_122
  cases assump_121
  case inl assump_125 =>
    cases assump_20
    case intro assump_129 assump_130 =>
      cases assump_129
      case inl assump_131 =>
        have assump_213 : ((p5 ∨ True) ∨ (p5 ∧ True)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_137 := assump_130 assump_213
        apply False.elim assump_137
      case inr assump_132 =>
        cases assump_132
        case inl assump_141 =>
          cases assump_141
          case intro assump_143 assump_144 =>
            have assump_214 : ((p5 ∨ True) ∨ (p5 ∧ True)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_151 := assump_130 assump_214
            apply False.elim assump_151
        case inr assump_142 =>
          cases assump_142
          case inl assump_155 =>
            apply False.elim assump_155
          case inr assump_156 =>
            have assump_215 : ((p5 ∨ True) ∨ (p5 ∧ True)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_163 := assump_130 assump_215
            apply False.elim assump_163
  case inr assump_126 =>
    cases assump_20
    case intro assump_169 assump_170 =>
      cases assump_169
      case inl assump_171 =>
        have assump_216 : ((p5 ∨ True) ∨ (p5 ∧ True)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_177 := assump_170 assump_216
        apply False.elim assump_177
      case inr assump_172 =>
        cases assump_172
        case inl assump_181 =>
          cases assump_181
          case intro assump_183 assump_184 =>
            have assump_217 : ((p5 ∨ True) ∨ (p5 ∧ True)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_191 := assump_170 assump_217
            apply False.elim assump_191
        case inr assump_182 =>
          cases assump_182
          case inl assump_195 =>
            apply False.elim assump_195
          case inr assump_196 =>
            have assump_218 : ((p5 ∨ True) ∨ (p5 ∧ True)) := by
              apply Or.inl
              apply Or.inr
              apply True.intro
            let assump_203 := assump_170 assump_218
            apply False.elim assump_203


variable (p5 p4 p3 p2 : Prop)
theorem file59_90381 : (((((False ∨ p4) → (p3 → False)) → False) ∧ (((p5 → p5) → False) ∧ ((False → True) ∨ (p2 → False)))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_11
    case intro assump_14 assump_15 =>
      cases assump_15
      case inl assump_18 =>
        have assump_40 : (p5 → p5) := by
          intro assump_24
          exact assump_24
        let assump_23 := assump_14 assump_40
        apply False.elim assump_23
      case inr assump_19 =>
        have assump_41 : (p5 → p5) := by
          intro assump_34
          exact assump_34
        let assump_33 := assump_14 assump_41
        apply False.elim assump_33


variable (p2 p7 p6 p5 p4 p1 p0 p3 : Prop)
theorem file59_91115 : ((((((False → False) → (p7 → p0)) → ((p3 → p7) → False)) → (((p6 → p4) → False) ∧ ((p5 ∧ p1) ∧ (p3 ∧ p0)))) ∧ ((((False → False) ∧ (p1 → p6)) ∧ ((p7 → p6) → (p5 → False))) ∧ (((p6 → p7) → False) ∧ ((p2 → True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            have assump_29 : (p2 → True) := by
              intro assump_25
              apply True.intro
            let assump_24 := assump_19 assump_29
            apply False.elim assump_24


variable (p4 p3 p0 p1 : Prop)
theorem file59_91918 : (((((p4 → False) ∧ (p1 → False)) → ((p0 → False) → (False → p3))) → False) → False) := by
  intro assump_1
  have assump_13 : (((p4 → False) ∧ (p1 → False)) → ((p0 → False) → (False → p3))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p2 p6 p4 p5 p0 p7 : Prop)
theorem file59_92326 : (((((p5 ∧ p2) ∧ (p2 ∧ p6)) ∧ ((p5 → p0) ∨ (p6 → p4))) ∨ (((p0 ∧ False) → (p7 ∧ p7)) → ((False ∧ p2) → False))) ∨ ((((p0 ∧ p4) → (p5 ∧ True)) ∨ ((p5 → False) ∨ (p5 → p4))) ∧ (((False → False) → (p0 → p7)) → ((p7 → p6) → False)))) := by
  apply Or.inl
  apply Or.inr
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply False.elim assump_3


variable (p3 p7 p1 p0 : Prop)
theorem file59_92760 : (((((p1 → False) ∧ (p7 ∨ p3)) → False) ∧ (((p0 → False) ∧ (False ∧ p0)) ∧ ((p7 → False) ∨ (p3 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_12


variable (p5 p4 p2 p7 : Prop)
theorem file59_93219 : ((((((p5 ∧ True) ∨ (p7 → p4)) ∧ ((False → False) → False)) → False) ∧ ((((False ∨ p2) ∧ (False ∧ p4)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_25 : (((False ∨ p2) ∧ (False ∧ p4)) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          apply False.elim assump_12
        case inr assump_13 =>
          cases assump_11
          case intro assump_18 assump_19 =>
            apply False.elim assump_18
    let assump_8 := assump_3 assump_25
    apply False.elim assump_8


variable (p5 p2 p0 p1 p4 : Prop)
theorem file59_93928 : (((((p2 ∨ p5) ∨ (p0 ∧ False)) → False) ∧ (((True ∧ True) → False) ∧ ((p4 → False) ∧ (p1 ∨ p1)))) → ((((p2 → False) ∧ (p4 ∧ False)) → False) ∨ (((p0 ∧ p2) ∧ (p2 → False)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          apply Or.inl
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            cases assump_20
            case intro assump_23 assump_24 =>
              apply False.elim assump_24
        case inr assump_15 =>
          apply Or.inl
          intro assump_31
          cases assump_31
          case intro assump_32 assump_33 =>
            cases assump_33
            case intro assump_36 assump_37 =>
              apply False.elim assump_37


variable (p2 p3 p4 p0 : Prop)
theorem file59_94905 : (((((p3 → False) → (False ∨ p0)) → ((p2 ∧ p0) → (True ∨ p4))) → False) → False) := by
  intro assump_5
  have assump_22 : (((p3 → False) → (False ∨ p0)) → ((p2 ∧ p0) → (True ∨ p4))) := by
    intro assump_9
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      apply Or.inl
      apply True.intro
  let assump_8 := assump_5 assump_22
  apply False.elim assump_8


variable (p7 p0 p6 p4 p1 : Prop)
theorem file59_95354 : (((((p6 ∨ p7) → False) → False) → False) → ((((p6 ∨ p0) ∨ (True → False)) → ((p0 ∨ p1) ∧ (p0 ∨ p4))) ∨ (((False → False) → False) → ((p1 ∧ True) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  cases assump_4
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      have assump_57 : (((p6 ∨ p7) → False) → False) := by
        intro assump_13
        have assump_58 : (p6 ∨ p7) := by
          apply Or.inl
          exact assump_7
        let assump_16 := assump_13 assump_58
        apply False.elim assump_16
      let assump_12 := assump_1 assump_57
      apply False.elim assump_12
    case inr assump_8 =>
      apply Or.inl
      exact assump_8
  case inr assump_6 =>
    have assump_59 : True := by
      apply True.intro
    let assump_27 := assump_6 assump_59
    apply False.elim assump_27
  cases assump_4
  case inl assump_31 =>
    cases assump_31
    case inl assump_33 =>
      have assump_60 : (((p6 ∨ p7) → False) → False) := by
        intro assump_39
        have assump_61 : (p6 ∨ p7) := by
          apply Or.inl
          exact assump_33
        let assump_42 := assump_39 assump_61
        apply False.elim assump_42
      let assump_38 := assump_1 assump_60
      apply False.elim assump_38
    case inr assump_34 =>
      apply Or.inl
      exact assump_34
  case inr assump_32 =>
    have assump_62 : True := by
      apply True.intro
    let assump_53 := assump_32 assump_62
    apply False.elim assump_53


variable (p3 p7 p1 p5 p4 p6 p0 : Prop)
theorem file59_96905 : (((((p3 ∨ True) ∧ (p7 → p5)) ∧ ((p7 → p6) ∧ (True → False))) → (((True ∧ p5) ∧ (p6 → p4)) → ((False → False) → (p7 → p0)))) ∧ ((((p0 ∨ p7) ∨ (p7 → p1)) → False) → False)) := by
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_1
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          cases assump_21
          case inl assump_23 =>
            cases assump_20
            case intro assump_29 assump_30 =>
              have assump_68 : True := by
                apply True.intro
              let assump_35 := assump_30 assump_68
              apply False.elim assump_35
          case inr assump_24 =>
            cases assump_20
            case intro assump_43 assump_44 =>
              have assump_69 : True := by
                apply True.intro
              let assump_49 := assump_44 assump_69
              apply False.elim assump_49
  intro assump_53
  have assump_70 : ((p0 ∨ p7) ∨ (p7 → p1)) := by
    apply Or.inr
    intro assump_57
    have assump_71 : ((p0 ∨ p7) ∨ (p7 → p1)) := by
      apply Or.inl
      apply Or.inr
      exact assump_57
    let assump_61 := assump_53 assump_71
    apply False.elim assump_61
  let assump_56 := assump_53 assump_70
  apply False.elim assump_56


variable (p3 p4 p1 p5 p7 p6 p2 : Prop)
theorem file59_98394 : (((((p2 ∧ False) ∧ (p4 ∧ p7)) → False) → False) → ((((p6 ∨ p3) ∧ (p7 ∨ p2)) → ((p5 → False) → (p2 → False))) → (((p3 → False) ∨ (p7 ∧ p1)) ∧ ((False ∧ False) ∧ (p4 → p3))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply Or.inl
  intro assump_7
  have assump_78 : (((p2 ∧ False) ∧ (p4 ∧ p7)) → False) := by
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        apply False.elim assump_16
  let assump_11 := assump_1 assump_78
  apply False.elim assump_11
  apply And.intro
  apply And.intro
  have assump_79 : (((p2 ∧ False) ∧ (p4 ∧ p7)) → False) := by
    intro assump_29
    cases assump_29
    case intro assump_30 assump_31 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        apply False.elim assump_33
  let assump_28 := assump_1 assump_79
  apply False.elim assump_28
  have assump_80 : (((p2 ∧ False) ∧ (p4 ∧ p7)) → False) := by
    intro assump_46
    cases assump_46
    case intro assump_47 assump_48 =>
      cases assump_47
      case intro assump_49 assump_50 =>
        apply False.elim assump_50
  let assump_45 := assump_1 assump_80
  apply False.elim assump_45
  intro assump_58
  have assump_81 : (((p2 ∧ False) ∧ (p4 ∧ p7)) → False) := by
    intro assump_66
    cases assump_66
    case intro assump_67 assump_68 =>
      cases assump_67
      case intro assump_69 assump_70 =>
        apply False.elim assump_70
  let assump_65 := assump_1 assump_81
  apply False.elim assump_65


variable (p4 p2 p3 p1 p5 p6 p7 : Prop)
theorem file59_99991 : (((((p3 → p1) → False) → ((p6 ∧ p7) ∨ (p1 → False))) ∧ (((p4 → True) → False) ∧ ((p7 → False) ∨ (p5 → p5)))) → ((((p4 ∧ False) → False) → False) → (((p2 ∨ p7) → (p5 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      cases assump_13
      case inl assump_16 =>
        have assump_34 : (p4 → True) := by
          intro assump_22
          apply True.intro
        let assump_21 := assump_12 assump_34
        apply False.elim assump_21
      case inr assump_17 =>
        have assump_35 : (p4 → True) := by
          intro assump_30
          apply True.intro
        let assump_29 := assump_12 assump_35
        apply False.elim assump_29


variable (p2 p3 p1 p7 p4 p0 p5 p6 : Prop)
theorem file59_100838 : (((((p3 ∧ p7) ∨ (True → False)) → ((p5 → False) ∧ (p6 ∧ False))) ∧ (((p2 ∧ False) ∧ (p4 → p7)) ∧ ((p4 ∧ p0) ∧ (True ∨ p3)))) → ((((p3 ∧ p6) ∧ (p0 → False)) → False) ∨ (((p4 ∧ p3) ∨ (p4 → p7)) → ((p0 ∨ p1) → (p1 ∨ p5))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11


variable (p5 p4 p1 p7 p6 p0 : Prop)
theorem file59_101409 : ((((((True ∧ p4) → False) ∨ ((False → False) ∨ (p7 → False))) ∨ (((p4 → p1) ∧ (True ∨ p6)) → ((p5 ∧ p0) → (p6 ∨ True)))) ∧ ((((False → False) → (True → True)) → False) ∧ (((p1 ∧ False) → (True ∨ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          have assump_86 : ((p1 ∧ False) → (True ∨ p0)) := by
            intro assump_17
            cases assump_17
            case intro assump_18 assump_19 =>
              apply False.elim assump_19
          let assump_16 := assump_11 assump_86
          apply False.elim assump_16
      case inr assump_7 =>
        cases assump_7
        case inl assump_27 =>
          cases assump_3
          case intro assump_31 assump_32 =>
            have assump_87 : ((p1 ∧ False) → (True ∨ p0)) := by
              intro assump_38
              cases assump_38
              case intro assump_39 assump_40 =>
                apply False.elim assump_40
            let assump_37 := assump_32 assump_87
            apply False.elim assump_37
        case inr assump_28 =>
          cases assump_3
          case intro assump_50 assump_51 =>
            have assump_88 : ((p1 ∧ False) → (True ∨ p0)) := by
              intro assump_57
              cases assump_57
              case intro assump_58 assump_59 =>
                apply False.elim assump_59
            let assump_56 := assump_51 assump_88
            apply False.elim assump_56
    case inr assump_5 =>
      cases assump_3
      case intro assump_69 assump_70 =>
        have assump_89 : ((p1 ∧ False) → (True ∨ p0)) := by
          intro assump_76
          cases assump_76
          case intro assump_77 assump_78 =>
            apply False.elim assump_78
        let assump_75 := assump_70 assump_89
        apply False.elim assump_75


variable (p6 p7 p1 p5 p4 p2 : Prop)
theorem file59_103424 : ((((((p7 ∧ p5) → False) → False) → False) ∧ ((((True → p4) → False) → ((p1 ∧ False) → (p6 → False))) ∧ (((p6 ∨ p2) ∨ (p6 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_24 : ((p6 ∨ p2) ∨ (p6 → False)) := by
        apply Or.inr
        intro assump_13
        have assump_25 : ((p6 ∨ p2) ∨ (p6 → False)) := by
          apply Or.inl
          apply Or.inl
          exact assump_13
        let assump_17 := assump_7 assump_25
        apply False.elim assump_17
      let assump_12 := assump_7 assump_24
      apply False.elim assump_12


variable (p3 p2 p5 p7 : Prop)
theorem file59_104143 : ((((((p2 → p7) ∧ (p5 → True)) → False) → (((True → False) → (p5 → p2)) ∨ ((p3 ∧ p5) ∧ (p7 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p2 → p7) ∧ (p5 → True)) → False) → (((True → False) → (p5 → p2)) ∨ ((p3 ∧ p5) ∧ (p7 ∧ False)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    have assump_22 : True := by
      apply True.intro
    let assump_14 := assump_8 assump_22
    apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p3 p0 p6 p4 p2 p5 p7 : Prop)
theorem file59_104739 : (((((p3 ∨ p4) ∨ (p0 ∨ p7)) → ((p6 → p3) → (p3 → p2))) ∧ (((True → False) ∧ (p4 ∧ p3)) ∧ ((p5 ∨ p3) ∧ (False → True)))) → False) := by
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
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              have assump_46 : True := by
                apply True.intro
              let assump_30 := assump_8 assump_46
              apply False.elim assump_30
            case inr assump_21 =>
              have assump_47 : True := by
                apply True.intro
              let assump_42 := assump_8 assump_47
              apply False.elim assump_42


variable (p1 p6 p5 p2 p0 p4 p3 : Prop)
theorem file59_105680 : (((((p6 ∧ p3) → (p6 → False)) ∧ ((p0 ∧ p4) ∨ (p3 → p4))) ∧ (((p2 ∨ p1) ∧ (p1 → False)) ∧ ((p5 ∧ p0) ∨ (False → False)))) → ((((p3 → False) ∧ (False ∧ p0)) ∧ ((p1 ∨ p0) ∨ (p3 → p5))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        apply False.elim assump_9


variable (p4 p7 p0 p6 p5 : Prop)
theorem file59_106169 : (((((p4 ∨ p0) → (False → False)) → False) ∨ (((p7 → False) → False) ∧ ((True ∨ p6) → False))) → ((((p5 → False) ∨ (p5 → False)) ∧ ((p7 → False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case inl assump_11 =>
        have assump_59 : ((p4 ∨ p0) → (False → False)) := by
          intro assump_16
          intro assump_17
          apply False.elim assump_17
        let assump_15 := assump_11 assump_59
        apply False.elim assump_15
      case inr assump_12 =>
        cases assump_12
        case intro assump_23 assump_24 =>
          have assump_60 : (True ∨ p6) := by
            apply Or.inl
            apply True.intro
          let assump_29 := assump_24 assump_60
          apply False.elim assump_29
    case inr assump_6 =>
      cases assump_1
      case inl assump_37 =>
        have assump_61 : ((p4 ∨ p0) → (False → False)) := by
          intro assump_42
          intro assump_43
          apply False.elim assump_43
        let assump_41 := assump_37 assump_61
        apply False.elim assump_41
      case inr assump_38 =>
        cases assump_38
        case intro assump_49 assump_50 =>
          have assump_62 : (True ∨ p6) := by
            apply Or.inl
            apply True.intro
          let assump_55 := assump_50 assump_62
          apply False.elim assump_55


variable (p1 p3 p5 : Prop)
theorem file59_107656 : (((((True ∧ p3) ∧ (p5 → False)) ∨ ((p3 ∨ False) → (p1 → True))) → False) → False) := by
  intro assump_1
  have assump_10 : (((True ∧ p3) ∧ (p5 → False)) ∨ ((p3 ∨ False) → (p1 → True))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p4 p6 p1 : Prop)
theorem file59_108040 : ((((((p4 → False) ∧ (p4 → True)) → False) → (((p1 ∧ False) ∧ (p6 ∧ p4)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p4 → False) ∧ (p4 → True)) → False) → (((p1 ∧ False) ∧ (p6 ∧ p4)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p1 p5 p6 p0 p4 p3 : Prop)
theorem file59_108584 : ((((((p1 → False) ∨ (p3 → p6)) → ((True → False) ∨ (p6 → False))) ∧ (((p6 ∧ p3) ∧ (p4 → False)) ∧ ((p6 ∨ p7) ∧ (p6 → False)))) ∧ ((((p4 → False) ∧ (p7 ∨ True)) ∨ ((p7 → p7) → (p4 → False))) ∨ (((p0 ∧ p0) → (p1 → p1)) ∨ ((p3 ∨ p5) ∨ (p3 → p1))))) → False) := by
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
            cases assump_9
            case intro assump_20 assump_21 =>
              cases assump_20
              case inl assump_22 =>
                cases assump_3
                case inl assump_28 =>
                  cases assump_28
                  case inl assump_30 =>
                    cases assump_30
                    case intro assump_32 assump_33 =>
                      cases assump_33
                      case inl assump_36 =>
                        have assump_174 : p6 := by
                          exact assump_22
                        let assump_42 := assump_21 assump_174
                        apply False.elim assump_42
                      case inr assump_37 =>
                        have assump_175 : p6 := by
                          exact assump_22
                        let assump_49 := assump_21 assump_175
                        apply False.elim assump_49
                  case inr assump_31 =>
                    have assump_176 : p6 := by
                      exact assump_22
                    let assump_60 := assump_21 assump_176
                    apply False.elim assump_60
                case inr assump_29 =>
                  cases assump_29
                  case inl assump_64 =>
                    have assump_177 : p6 := by
                      exact assump_22
                    let assump_69 := assump_21 assump_177
                    apply False.elim assump_69
                  case inr assump_65 =>
                    cases assump_65
                    case inl assump_73 =>
                      cases assump_73
                      case inl assump_75 =>
                        have assump_178 : p6 := by
                          exact assump_22
                        let assump_80 := assump_21 assump_178
                        apply False.elim assump_80
                      case inr assump_76 =>
                        have assump_179 : p6 := by
                          exact assump_22
                        let assump_87 := assump_21 assump_179
                        apply False.elim assump_87
                    case inr assump_74 =>
                      have assump_180 : p6 := by
                        exact assump_22
                      let assump_95 := assump_21 assump_180
                      apply False.elim assump_95
              case inr assump_23 =>
                cases assump_3
                case inl assump_103 =>
                  cases assump_103
                  case inl assump_105 =>
                    cases assump_105
                    case intro assump_107 assump_108 =>
                      cases assump_108
                      case inl assump_111 =>
                        have assump_181 : p6 := by
                          exact assump_12
                        let assump_117 := assump_21 assump_181
                        apply False.elim assump_117
                      case inr assump_112 =>
                        have assump_182 : p6 := by
                          exact assump_12
                        let assump_124 := assump_21 assump_182
                        apply False.elim assump_124
                  case inr assump_106 =>
                    have assump_183 : p6 := by
                      exact assump_12
                    let assump_135 := assump_21 assump_183
                    apply False.elim assump_135
                case inr assump_104 =>
                  cases assump_104
                  case inl assump_139 =>
                    have assump_184 : p6 := by
                      exact assump_12
                    let assump_144 := assump_21 assump_184
                    apply False.elim assump_144
                  case inr assump_140 =>
                    cases assump_140
                    case inl assump_148 =>
                      cases assump_148
                      case inl assump_150 =>
                        have assump_185 : p6 := by
                          exact assump_12
                        let assump_155 := assump_21 assump_185
                        apply False.elim assump_155
                      case inr assump_151 =>
                        have assump_186 : p6 := by
                          exact assump_12
                        let assump_162 := assump_21 assump_186
                        apply False.elim assump_162
                    case inr assump_149 =>
                      have assump_187 : p6 := by
                        exact assump_12
                      let assump_170 := assump_21 assump_187
                      apply False.elim assump_170


variable (p1 p5 p7 p4 p3 p6 : Prop)
theorem file59_113829 : (((((p7 → False) ∧ (p5 ∧ p1)) → False) → (((p1 → p3) ∧ (p5 → False)) → ((p6 ∧ p1) → (False ∧ p7)))) → ((((False ∨ True) → False) → ((p3 ∧ p5) ∧ (p4 ∧ p3))) ∨ (((p4 → False) → (p5 → False)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  apply And.intro
  have assump_29 : (False ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_7 := assump_4 assump_29
  apply False.elim assump_7
  have assump_30 : (False ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_13 := assump_4 assump_30
  apply False.elim assump_13
  apply And.intro
  have assump_31 : (False ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_19 := assump_4 assump_31
  apply False.elim assump_19
  have assump_32 : (False ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_25 := assump_4 assump_32
  apply False.elim assump_25


variable (p0 p1 p2 p3 p4 p6 : Prop)
theorem file59_114776 : (((((p6 ∨ p2) ∨ (True ∧ p0)) ∧ ((False ∧ p4) ∧ (p0 → False))) → False) ∨ ((((p4 ∨ p4) ∧ (p6 → p0)) → False) ∧ (((False → False) ∧ (False → p1)) ∧ ((p2 → p3) → (False ∨ p0))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_12
      case inr assump_7 =>
        cases assump_3
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            apply False.elim assump_20
    case inr assump_5 =>
      cases assump_5
      case intro assump_24 assump_25 =>
        cases assump_3
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            apply False.elim assump_32


variable (p6 p1 p3 : Prop)
theorem file59_115819 : ((((((False → False) → False) ∧ ((p1 ∨ True) ∧ (p3 → False))) → False) → ((((True → False) → False) → ((p1 ∨ p6) ∨ (False → False))) → False)) → False) := by
  intro assump_1
  have assump_49 : ((((False → False) → False) ∧ ((p1 ∨ True) ∧ (p3 → False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          have assump_50 : (False → False) := by
            intro assump_21
            apply False.elim assump_21
          let assump_20 := assump_6 assump_50
          apply False.elim assump_20
        case inr assump_13 =>
          have assump_51 : (False → False) := by
            intro assump_33
            apply False.elim assump_33
          let assump_32 := assump_6 assump_51
          apply False.elim assump_32
  let assump_4 := assump_1 assump_49
  have assump_52 : (((True → False) → False) → ((p1 ∨ p6) ∨ (False → False))) := by
    intro assump_40
    apply Or.inr
    intro assump_43
    apply False.elim assump_43
  let assump_39 := assump_4 assump_52
  apply False.elim assump_39


variable (p5 p0 p1 p3 p4 : Prop)
theorem file59_117038 : (((((p4 → p5) → False) ∧ ((p1 ∧ p0) ∧ (True → False))) ∧ (((True ∧ p3) ∧ (p3 → False)) ∧ ((False → False) → (False → p0)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                have assump_41 : p3 := by
                  exact assump_23
                let assump_37 := assump_21 assump_41
                apply False.elim assump_37


variable (p0 p2 p4 p3 : Prop)
theorem file59_117871 : ((((((True ∧ p4) ∨ (p3 → True)) ∨ ((p3 → False) ∧ (p0 ∧ True))) → (((False → False) → False) → ((p2 ∧ p2) ∨ (p2 → p2)))) → False) → False) := by
  intro assump_1
  have assump_43 : ((((True ∧ p4) ∨ (p3 → True)) ∨ ((p3 → False) ∧ (p0 ∧ True))) → (((False → False) → False) → ((p2 ∧ p2) ∨ (p2 → p2)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply Or.inr
          intro assump_19
          exact assump_19
      case inr assump_12 =>
        apply Or.inr
        intro assump_24
        exact assump_24
    case inr assump_10 =>
      cases assump_10
      case intro assump_27 assump_28 =>
        cases assump_28
        case intro assump_31 assump_32 =>
          apply Or.inr
          intro assump_37
          exact assump_37
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p5 p7 p4 p0 p6 p3 p1 p2 : Prop)
theorem file59_118906 : ((((((False ∨ True) ∧ (p2 ∧ p4)) → False) ∧ (((p5 → p7) → (True → False)) ∧ ((p7 ∧ False) ∨ (p5 ∧ p0)))) ∧ ((((p3 ∧ p1) → (p5 ∧ p6)) ∧ ((p0 ∧ p3) ∧ (True → False))) ∧ (((p0 ∨ p5) → (p2 → p0)) ∨ ((p0 ∧ p0) → (p2 → False))))) → False) := by
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    cases assump_23
    case intro assump_25 assump_26 =>
      cases assump_26
      case intro assump_29 assump_30 =>
        cases assump_30
        case inl assump_33 =>
          cases assump_33
          case intro assump_35 assump_36 =>
            apply False.elim assump_36
        case inr assump_34 =>
          cases assump_34
          case intro assump_41 assump_42 =>
            cases assump_24
            case intro assump_47 assump_48 =>
              cases assump_47
              case intro assump_49 assump_50 =>
                cases assump_50
                case intro assump_53 assump_54 =>
                  cases assump_53
                  case intro assump_55 assump_56 =>
                    cases assump_48
                    case inl assump_63 =>
                      have assump_81 : True := by
                        apply True.intro
                      let assump_69 := assump_54 assump_81
                      apply False.elim assump_69
                    case inr assump_64 =>
                      have assump_82 : True := by
                        apply True.intro
                      let assump_77 := assump_54 assump_82
                      apply False.elim assump_77


