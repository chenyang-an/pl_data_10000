variable (p0 p2 p3 p7 p4 p5 p6 : Prop)
theorem file4_47 : (((((p7 ∧ p2) → (True ∧ p2)) ∧ ((p4 ∧ False) → (p2 → False))) → (((p6 → p2) ∨ (p5 ∧ p5)) → ((False ∨ True) → False))) → ((((p0 ∧ p3) → (p3 → True)) ∨ ((False → False) ∨ (p5 ∨ p6))) ∨ (((False ∧ p2) ∧ (p4 → False)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  apply True.intro


variable (p4 p2 p0 p6 p5 p3 p7 p1 : Prop)
theorem file4_444 : (((((p5 → False) → False) ∧ ((p1 → False) ∧ (p6 ∧ False))) → False) ∨ ((((p7 ∧ p4) → (p7 ∨ p2)) → ((p4 → False) → (p3 → p3))) ∧ (((False ∨ p0) ∨ (p5 → False)) ∨ ((False ∨ p1) ∧ (p6 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply False.elim assump_11


variable (p2 p0 p7 p6 : Prop)
theorem file4_932 : (((((p6 → p2) ∧ (True → False)) → False) ∧ (((p0 ∧ p7) ∧ (p2 ∧ False)) ∧ ((p0 → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            apply False.elim assump_17


variable (p0 p3 p6 p7 p2 p5 : Prop)
theorem file4_1460 : (((((p7 → p7) → (p3 → p2)) → ((False → False) ∨ (True ∧ True))) ∨ (((p6 → False) ∧ (p2 → True)) ∨ ((p2 ∨ p7) ∧ (p5 ∧ False)))) ∨ ((((p0 → False) → (p5 → False)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p6 p0 p7 p3 p1 : Prop)
theorem file4_1810 : (((((True ∨ p3) ∧ (False → p3)) → ((True → False) ∧ (p1 ∧ p3))) → (((True → False) ∨ (True → False)) → ((p6 → p0) ∧ (p1 ∨ p7)))) ∨ ((((False → p6) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    have assump_62 : ((True ∨ p3) ∧ (False → p3)) := by
      apply And.intro
      apply Or.inl
      apply True.intro
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_1 assump_62
    let assump_16 := And.left assump_12
    have assump_63 : True := by
      apply True.intro
    let assump_17 := assump_16 assump_63
    apply False.elim assump_17
  case inr assump_7 =>
    have assump_64 : ((True ∨ p3) ∧ (False → p3)) := by
      apply And.intro
      apply Or.inl
      apply True.intro
      intro assump_26
      apply False.elim assump_26
    let assump_25 := assump_1 assump_64
    let assump_29 := And.left assump_25
    have assump_65 : True := by
      apply True.intro
    let assump_30 := assump_29 assump_65
    apply False.elim assump_30
  cases assump_2
  case inl assump_34 =>
    have assump_66 : ((True ∨ p3) ∧ (False → p3)) := by
      apply And.intro
      apply Or.inl
      apply True.intro
      intro assump_41
      apply False.elim assump_41
    let assump_40 := assump_1 assump_66
    let assump_44 := And.left assump_40
    have assump_67 : True := by
      apply True.intro
    let assump_45 := assump_44 assump_67
    apply False.elim assump_45
  case inr assump_35 =>
    have assump_68 : ((True ∨ p3) ∧ (False → p3)) := by
      apply And.intro
      apply Or.inl
      apply True.intro
      intro assump_54
      apply False.elim assump_54
    let assump_53 := assump_1 assump_68
    let assump_57 := And.left assump_53
    have assump_69 : True := by
      apply True.intro
    let assump_58 := assump_57 assump_69
    apply False.elim assump_58


variable (p2 p7 p6 p1 p5 p0 p3 : Prop)
theorem file4_3794 : ((((((p7 ∨ True) → (True ∧ p6)) → False) → False) ∧ ((((p3 → p6) → (p2 ∧ p3)) → ((p1 ∨ p7) ∨ (p0 → p7))) ∧ (((p5 → False) ∧ (True ∧ True)) ∧ ((p6 ∧ True) ∧ (True → False))))) → False) := by
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
            case intro assump_22 assump_23 =>
              cases assump_22
              case intro assump_24 assump_25 =>
                have assump_36 : True := by
                  apply True.intro
                let assump_32 := assump_23 assump_36
                apply False.elim assump_32


variable (p4 p1 p5 p0 p7 : Prop)
theorem file4_4688 : ((((((False ∨ p4) ∧ (p7 → False)) → False) ∨ (((p7 → False) → (p1 → False)) ∧ ((False ∨ True) → (True → False)))) ∧ ((((p1 ∨ p4) → False) → ((False ∧ p5) → (p0 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_44 : (((p1 ∨ p4) → False) → ((False ∧ p5) → (p0 → False))) := by
        intro assump_11
        intro assump_12
        intro assump_13
        cases assump_12
        case intro assump_16 assump_17 =>
          apply False.elim assump_16
      let assump_10 := assump_3 assump_44
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_23 assump_24 =>
        have assump_45 : (((p1 ∨ p4) → False) → ((False ∧ p5) → (p0 → False))) := by
          intro assump_32
          intro assump_33
          intro assump_34
          cases assump_33
          case intro assump_37 assump_38 =>
            apply False.elim assump_37
        let assump_31 := assump_3 assump_45
        apply False.elim assump_31


variable (p3 p1 p0 p5 : Prop)
theorem file4_5820 : ((((((p0 ∨ p5) → False) → ((False ∧ p3) ∧ (p5 → False))) → (((p1 ∧ p3) ∧ (True ∧ p1)) → ((p1 ∨ p0) ∨ (p0 → False)))) → False) → False) := by
  intro assump_5
  have assump_30 : ((((p0 ∨ p5) → False) → ((False ∧ p3) ∧ (p5 → False))) → (((p1 ∧ p3) ∧ (True ∧ p1)) → ((p1 ∨ p0) ∨ (p0 → False)))) := by
    intro assump_9
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        cases assump_12
        case intro assump_19 assump_20 =>
          apply Or.inl
          apply Or.inl
          exact assump_20
  let assump_8 := assump_5 assump_30
  apply False.elim assump_8


variable (p2 p4 p1 p0 p3 p7 p5 : Prop)
theorem file4_6543 : ((((((p7 ∧ p4) → (False → False)) ∨ ((p2 → p5) ∧ (p0 ∨ p5))) → False) ∧ ((((False → False) ∨ (p7 ∧ True)) → False) ∧ (((p0 ∨ True) ∧ (False → p3)) ∨ ((True → p5) ∨ (p1 → p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            have assump_64 : ((False → False) ∨ (p7 ∧ True)) := by
              apply Or.inl
              intro assump_23
              apply False.elim assump_23
            let assump_22 := assump_6 assump_64
            apply False.elim assump_22
          case inr assump_15 =>
            have assump_65 : ((False → False) ∨ (p7 ∧ True)) := by
              apply Or.inl
              intro assump_35
              apply False.elim assump_35
            let assump_34 := assump_6 assump_65
            apply False.elim assump_34
      case inr assump_11 =>
        cases assump_11
        case inl assump_41 =>
          have assump_66 : ((False → False) ∨ (p7 ∧ True)) := by
            apply Or.inl
            intro assump_48
            apply False.elim assump_48
          let assump_47 := assump_6 assump_66
          apply False.elim assump_47
        case inr assump_42 =>
          have assump_67 : ((False → False) ∨ (p7 ∧ True)) := by
            apply Or.inl
            intro assump_58
            apply False.elim assump_58
          let assump_57 := assump_6 assump_67
          apply False.elim assump_57


variable (p3 p5 p1 p6 p7 p0 p2 : Prop)
theorem file4_8223 : (((((p2 → False) ∧ (p3 ∨ False)) → ((p2 ∨ p5) → (p2 → False))) → False) → ((((p3 ∨ p1) → False) ∨ ((p2 → p7) → False)) ∧ (((p1 ∨ p1) → False) ∧ ((p6 ∨ p0) ∧ (p5 ∨ p7))))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    have assump_298 : (((p2 → False) ∧ (p3 ∨ False)) → ((p2 ∨ p5) → (p2 → False))) := by
      intro assump_11
      intro assump_12
      intro assump_13
      cases assump_12
      case inl assump_16 =>
        cases assump_11
        case intro assump_20 assump_21 =>
          cases assump_21
          case inl assump_24 =>
            have assump_299 : p2 := by
              exact assump_16
            let assump_29 := assump_20 assump_299
            apply False.elim assump_29
          case inr assump_25 =>
            apply False.elim assump_25
      case inr assump_17 =>
        cases assump_11
        case intro assump_37 assump_38 =>
          cases assump_38
          case inl assump_41 =>
            have assump_300 : p2 := by
              exact assump_13
            let assump_46 := assump_37 assump_300
            apply False.elim assump_46
          case inr assump_42 =>
            apply False.elim assump_42
    let assump_10 := assump_1 assump_298
    apply False.elim assump_10
  case inr assump_6 =>
    have assump_301 : (((p2 → False) ∧ (p3 ∨ False)) → ((p2 ∨ p5) → (p2 → False))) := by
      intro assump_59
      intro assump_60
      intro assump_61
      cases assump_60
      case inl assump_64 =>
        cases assump_59
        case intro assump_68 assump_69 =>
          cases assump_69
          case inl assump_72 =>
            have assump_302 : p2 := by
              exact assump_64
            let assump_77 := assump_68 assump_302
            apply False.elim assump_77
          case inr assump_73 =>
            apply False.elim assump_73
      case inr assump_65 =>
        cases assump_59
        case intro assump_85 assump_86 =>
          cases assump_86
          case inl assump_89 =>
            have assump_303 : p2 := by
              exact assump_61
            let assump_94 := assump_85 assump_303
            apply False.elim assump_94
          case inr assump_90 =>
            apply False.elim assump_90
    let assump_58 := assump_1 assump_301
    apply False.elim assump_58
  apply And.intro
  intro assump_103
  cases assump_103
  case inl assump_104 =>
    have assump_304 : (((p2 → False) ∧ (p3 ∨ False)) → ((p2 ∨ p5) → (p2 → False))) := by
      intro assump_111
      intro assump_112
      intro assump_113
      cases assump_112
      case inl assump_116 =>
        cases assump_111
        case intro assump_120 assump_121 =>
          cases assump_121
          case inl assump_124 =>
            have assump_305 : p2 := by
              exact assump_116
            let assump_129 := assump_120 assump_305
            apply False.elim assump_129
          case inr assump_125 =>
            apply False.elim assump_125
      case inr assump_117 =>
        cases assump_111
        case intro assump_137 assump_138 =>
          cases assump_138
          case inl assump_141 =>
            have assump_306 : p2 := by
              exact assump_113
            let assump_146 := assump_137 assump_306
            apply False.elim assump_146
          case inr assump_142 =>
            apply False.elim assump_142
    let assump_110 := assump_1 assump_304
    apply False.elim assump_110
  case inr assump_105 =>
    have assump_307 : (((p2 → False) ∧ (p3 ∨ False)) → ((p2 ∨ p5) → (p2 → False))) := by
      intro assump_160
      intro assump_161
      intro assump_162
      cases assump_161
      case inl assump_165 =>
        cases assump_160
        case intro assump_169 assump_170 =>
          cases assump_170
          case inl assump_173 =>
            have assump_308 : p2 := by
              exact assump_165
            let assump_178 := assump_169 assump_308
            apply False.elim assump_178
          case inr assump_174 =>
            apply False.elim assump_174
      case inr assump_166 =>
        cases assump_160
        case intro assump_186 assump_187 =>
          cases assump_187
          case inl assump_190 =>
            have assump_309 : p2 := by
              exact assump_162
            let assump_195 := assump_186 assump_309
            apply False.elim assump_195
          case inr assump_191 =>
            apply False.elim assump_191
    let assump_159 := assump_1 assump_307
    apply False.elim assump_159
  apply And.intro
  have assump_310 : (((p2 → False) ∧ (p3 ∨ False)) → ((p2 ∨ p5) → (p2 → False))) := by
    intro assump_207
    intro assump_208
    intro assump_209
    cases assump_208
    case inl assump_212 =>
      cases assump_207
      case intro assump_216 assump_217 =>
        cases assump_217
        case inl assump_220 =>
          have assump_311 : p2 := by
            exact assump_212
          let assump_225 := assump_216 assump_311
          apply False.elim assump_225
        case inr assump_221 =>
          apply False.elim assump_221
    case inr assump_213 =>
      cases assump_207
      case intro assump_233 assump_234 =>
        cases assump_234
        case inl assump_237 =>
          have assump_312 : p2 := by
            exact assump_209
          let assump_242 := assump_233 assump_312
          apply False.elim assump_242
        case inr assump_238 =>
          apply False.elim assump_238
  let assump_206 := assump_1 assump_310
  apply False.elim assump_206
  have assump_313 : (((p2 → False) ∧ (p3 ∨ False)) → ((p2 ∨ p5) → (p2 → False))) := by
    intro assump_254
    intro assump_255
    intro assump_256
    cases assump_255
    case inl assump_259 =>
      cases assump_254
      case intro assump_263 assump_264 =>
        cases assump_264
        case inl assump_267 =>
          have assump_314 : p2 := by
            exact assump_259
          let assump_272 := assump_263 assump_314
          apply False.elim assump_272
        case inr assump_268 =>
          apply False.elim assump_268
    case inr assump_260 =>
      cases assump_254
      case intro assump_280 assump_281 =>
        cases assump_281
        case inl assump_284 =>
          have assump_315 : p2 := by
            exact assump_256
          let assump_289 := assump_280 assump_315
          apply False.elim assump_289
        case inr assump_285 =>
          apply False.elim assump_285
  let assump_253 := assump_1 assump_313
  apply False.elim assump_253


variable (p5 p4 p6 : Prop)
theorem file4_14775 : (((((p5 ∧ False) → False) → ((p6 ∨ p4) ∨ (p6 → False))) → False) → False) := by
  intro assump_1
  have assump_23 : (((p5 ∧ False) → False) → ((p6 ∨ p4) ∨ (p6 → False))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    have assump_24 : (((p5 ∧ False) → False) → ((p6 ∨ p4) ∨ (p6 → False))) := by
      intro assump_14
      apply Or.inl
      apply Or.inl
      exact assump_8
    let assump_13 := assump_1 assump_24
    apply False.elim assump_13
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p3 p6 p2 p0 p1 p5 : Prop)
theorem file4_15364 : ((((((True ∧ p6) → (True → False)) ∧ ((False ∨ False) ∧ (p5 → False))) ∧ (((p5 → False) ∨ (p6 → False)) ∧ ((p2 ∨ p3) ∨ (True → False)))) ∧ ((((p6 → False) ∨ (p0 ∧ p6)) → ((p6 → p3) ∨ (True → p1))) ∨ (((p3 → False) → (p6 → p1)) ∨ ((p5 ∨ False) ∨ (p0 ∧ p2))))) → False) := by
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_16
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        cases assump_21
        case intro assump_24 assump_25 =>
          cases assump_24
          case inl assump_26 =>
            apply False.elim assump_26
          case inr assump_27 =>
            apply False.elim assump_27


variable (p3 p6 p5 p2 p1 p4 p0 : Prop)
theorem file4_16127 : (((((True → False) → (p6 → False)) → False) ∧ (((p3 ∨ p2) ∨ (p3 ∨ p4)) → False)) → ((((p1 → p3) ∨ (False → p0)) → ((p5 → p6) → False)) → (((p3 → True) ∨ (p2 → False)) ∧ ((p3 → p2) ∨ (True → p5))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    apply Or.inl
    intro assump_11
    apply True.intro
  cases assump_1
  case intro assump_14 assump_15 =>
    apply Or.inl
    intro assump_20
    have assump_28 : ((p3 ∨ p2) ∨ (p3 ∨ p4)) := by
      apply Or.inl
      apply Or.inl
      exact assump_20
    let assump_24 := assump_15 assump_28
    apply False.elim assump_24


variable (p0 p6 p2 p3 p7 p4 : Prop)
theorem file4_16825 : (((((p2 ∧ p7) → (p7 ∧ p6)) ∨ ((p0 → p0) → (p4 ∨ p3))) → (((p6 ∨ p3) → (False → False)) → False)) → ((((p7 → False) → (p3 → False)) → ((p2 → False) → (p7 → False))) → (((p6 → p0) → False) → ((p2 → p2) ∧ (p2 → True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  exact assump_4
  intro assump_13
  apply True.intro


variable (p2 p0 p5 p1 : Prop)
theorem file4_17243 : (((((p0 → p2) ∨ (p5 ∧ p1)) → ((p5 ∧ p2) → (True ∨ p0))) → False) → False) := by
  intro assump_1
  have assump_26 : (((p0 → p2) ∨ (p5 ∧ p1)) → ((p5 ∧ p2) → (True ∨ p0))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case inl assump_13 =>
        apply Or.inl
        apply True.intro
      case inr assump_14 =>
        cases assump_14
        case intro assump_17 assump_18 =>
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p6 p7 p4 p3 p1 p2 p0 : Prop)
theorem file4_17879 : (((((True → False) ∧ (p7 → True)) ∨ ((p7 ∨ True) → False)) → (((p6 ∧ p3) → False) ∧ ((p4 ∧ p7) → False))) ∨ ((((p1 → p3) ∧ (p7 → False)) ∨ ((p3 ∧ p1) → False)) ∧ (((p1 → False) ∧ (p3 → False)) ∧ ((p2 → p0) ∧ (p3 → False))))) := by
  apply Or.inl
  intro assump_14
  apply And.intro
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_14
    case inl assump_22 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        have assump_68 : True := by
          apply True.intro
        let assump_31 := assump_24 assump_68
        apply False.elim assump_31
    case inr assump_23 =>
      have assump_69 : (p7 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_37 := assump_23 assump_69
      apply False.elim assump_37
  intro assump_41
  cases assump_41
  case intro assump_42 assump_43 =>
    cases assump_14
    case inl assump_48 =>
      cases assump_48
      case intro assump_50 assump_51 =>
        have assump_70 : True := by
          apply True.intro
        let assump_58 := assump_50 assump_70
        apply False.elim assump_58
    case inr assump_49 =>
      have assump_71 : (p7 ∨ True) := by
        apply Or.inl
        exact assump_43
      let assump_64 := assump_49 assump_71
      apply False.elim assump_64


variable (p0 p7 p1 p3 p6 p4 p5 : Prop)
theorem file4_19247 : (((((p0 ∧ p3) ∧ (p1 ∧ p0)) ∨ ((False ∧ p0) → (p7 → False))) → False) → ((((p1 → False) → (p0 ∨ p4)) ∧ ((p0 ∨ p0) ∧ (p6 → p4))) ∧ (((False ∧ p4) ∨ (p0 ∨ p5)) ∨ ((p7 ∨ True) ∧ (p0 → p5))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  have assump_68 : (((p0 ∧ p3) ∧ (p1 ∧ p0)) ∨ ((False ∧ p0) → (p7 → False))) := by
    apply Or.inr
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      apply False.elim assump_12
  let assump_7 := assump_1 assump_68
  apply False.elim assump_7
  apply And.intro
  have assump_69 : (((p0 ∧ p3) ∧ (p1 ∧ p0)) ∨ ((False ∧ p0) → (p7 → False))) := by
    apply Or.inr
    intro assump_22
    intro assump_23
    cases assump_22
    case intro assump_26 assump_27 =>
      apply False.elim assump_26
  let assump_21 := assump_1 assump_69
  apply False.elim assump_21
  intro assump_33
  have assump_70 : (((p0 ∧ p3) ∧ (p1 ∧ p0)) ∨ ((False ∧ p0) → (p7 → False))) := by
    apply Or.inr
    intro assump_39
    intro assump_40
    cases assump_39
    case intro assump_43 assump_44 =>
      apply False.elim assump_43
  let assump_38 := assump_1 assump_70
  apply False.elim assump_38
  apply Or.inr
  apply And.intro
  apply Or.inr
  apply True.intro
  intro assump_52
  have assump_71 : (((p0 ∧ p3) ∧ (p1 ∧ p0)) ∨ ((False ∧ p0) → (p7 → False))) := by
    apply Or.inr
    intro assump_57
    intro assump_58
    cases assump_57
    case intro assump_61 assump_62 =>
      apply False.elim assump_61
  let assump_56 := assump_1 assump_71
  apply False.elim assump_56


variable (p7 p1 p0 p2 p3 p5 : Prop)
theorem file4_20879 : (((((p2 ∨ p1) → (False → False)) → False) → (((False ∨ p1) ∨ (p7 → True)) ∨ ((p0 → p5) ∨ (p0 → False)))) ∨ ((((p5 → p3) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  apply True.intro


variable (p7 p6 p2 p0 p3 p1 p5 : Prop)
theorem file4_21194 : (((((p6 ∨ p7) ∨ (p5 → False)) → ((False → False) → False)) → (((p0 ∨ False) → False) ∨ ((p1 ∨ p0) → False))) → ((((True ∨ p1) ∨ (p2 ∧ False)) ∧ ((p0 ∨ p0) → (p3 ∨ p7))) → (((False ∧ p3) → False) → ((False → p5) ∧ (False → p3))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  apply False.elim assump_4
  intro assump_7
  apply False.elim assump_7


variable (p6 p4 p3 p7 p2 p0 p5 : Prop)
theorem file4_21652 : (((((p3 ∨ False) → (p5 ∧ p6)) → ((False ∧ p0) → (p2 ∨ p3))) → False) → ((((p2 ∨ p5) ∧ (True → False)) → ((p2 ∨ p7) ∧ (p7 → False))) → (((p6 → False) → (p4 ∧ p7)) ∧ ((False ∨ p7) → False)))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  apply And.intro
  have assump_57 : (((p3 ∨ False) → (p5 ∧ p6)) → ((False ∧ p0) → (p2 ∨ p3))) := by
    intro assump_11
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      apply False.elim assump_13
  let assump_10 := assump_1 assump_57
  apply False.elim assump_10
  have assump_58 : (((p3 ∨ False) → (p5 ∧ p6)) → ((False ∧ p0) → (p2 ∨ p3))) := by
    intro assump_27
    intro assump_28
    cases assump_28
    case intro assump_29 assump_30 =>
      apply False.elim assump_29
  let assump_26 := assump_1 assump_58
  apply False.elim assump_26
  intro assump_36
  cases assump_36
  case inl assump_37 =>
    apply False.elim assump_37
  case inr assump_38 =>
    have assump_59 : (((p3 ∨ False) → (p5 ∧ p6)) → ((False ∧ p0) → (p2 ∨ p3))) := by
      intro assump_48
      intro assump_49
      cases assump_49
      case intro assump_50 assump_51 =>
        apply False.elim assump_50
    let assump_47 := assump_1 assump_59
    apply False.elim assump_47


variable (p3 p0 p4 p7 : Prop)
theorem file4_22963 : (((((p7 → p4) ∧ (p7 ∧ p0)) → ((False → False) ∧ (p3 → p3))) → False) → False) := by
  intro assump_5
  have assump_29 : (((p7 → p4) ∧ (p7 ∧ p0)) → ((False → False) ∧ (p3 → p3))) := by
    intro assump_9
    apply And.intro
    intro assump_10
    apply False.elim assump_10
    intro assump_13
    cases assump_9
    case intro assump_16 assump_17 =>
      cases assump_17
      case intro assump_20 assump_21 =>
        exact assump_13
  let assump_8 := assump_5 assump_29
  apply False.elim assump_8


variable (p7 p1 p0 p3 p6 p5 p2 p4 : Prop)
theorem file4_23531 : (((((p6 ∧ p7) → (p4 ∨ p6)) ∨ ((p7 → p4) ∨ (p4 ∨ p5))) ∨ (((False → False) → False) → False)) ∨ ((((p7 ∨ p2) ∨ (p0 → False)) ∧ ((p1 → False) ∨ (False ∧ p1))) ∧ (((p1 → True) ∨ (p3 → False)) → ((False ∧ p0) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    apply Or.inr
    exact assump_12


variable (p0 p1 p3 p4 p7 p6 : Prop)
theorem file4_23968 : (((((False ∧ p1) ∧ (p4 → False)) → False) → False) → ((((p3 ∨ p6) → (p4 ∧ p0)) ∧ ((p3 ∨ p7) ∧ (True ∧ p7))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          have assump_53 : (((False ∧ p1) ∧ (p4 → False)) → False) := by
            intro assump_22
            cases assump_22
            case intro assump_23 assump_24 =>
              cases assump_23
              case intro assump_25 assump_26 =>
                apply False.elim assump_25
          let assump_21 := assump_1 assump_53
          apply False.elim assump_21
      case inr assump_10 =>
        cases assump_8
        case intro assump_34 assump_35 =>
          have assump_54 : (((False ∧ p1) ∧ (p4 → False)) → False) := by
            intro assump_43
            cases assump_43
            case intro assump_44 assump_45 =>
              cases assump_44
              case intro assump_46 assump_47 =>
                apply False.elim assump_46
          let assump_42 := assump_1 assump_54
          apply False.elim assump_42


variable (p0 p6 p2 p3 p7 : Prop)
theorem file4_25253 : (((((False → False) ∨ (p0 ∨ p6)) ∨ ((False ∨ p3) ∧ (p7 ∧ p2))) → False) → False) := by
  intro assump_1
  have assump_11 : (((False → False) ∨ (p0 ∨ p6)) ∨ ((False ∨ p3) ∧ (p7 ∧ p2))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p5 : Prop)
theorem file4_25639 : (((((p5 → False) ∧ (p4 → False)) → ((False ∧ p4) → (p5 → False))) → False) → False) := by
  intro assump_1
  have assump_17 : (((p5 → False) ∧ (p4 → False)) → ((False ∧ p4) → (p5 → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p0 p2 p4 p5 p1 p3 p7 p6 : Prop)
theorem file4_26113 : ((((((p3 ∧ True) → (p5 ∨ True)) ∨ ((True ∨ p2) ∨ (p0 → False))) ∧ (((p6 → p2) → False) → ((p7 ∧ p4) ∨ (p4 ∧ p5)))) ∧ ((((p5 ∧ p1) ∧ (p7 → p7)) → False) ∧ (((True → False) ∧ (p1 ∨ p0)) ∧ ((p3 → False) ∨ (p3 → p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_19
              case inl assump_22 =>
                cases assump_17
                case inl assump_26 =>
                  have assump_236 : True := by
                    apply True.intro
                  let assump_32 := assump_18 assump_236
                  apply False.elim assump_32
                case inr assump_27 =>
                  have assump_237 : True := by
                    apply True.intro
                  let assump_40 := assump_18 assump_237
                  apply False.elim assump_40
              case inr assump_23 =>
                cases assump_17
                case inl assump_46 =>
                  have assump_238 : True := by
                    apply True.intro
                  let assump_52 := assump_18 assump_238
                  apply False.elim assump_52
                case inr assump_47 =>
                  have assump_239 : True := by
                    apply True.intro
                  let assump_60 := assump_18 assump_239
                  apply False.elim assump_60
      case inr assump_7 =>
        cases assump_7
        case inl assump_64 =>
          cases assump_64
          case inl assump_66 =>
            cases assump_3
            case intro assump_72 assump_73 =>
              cases assump_73
              case intro assump_76 assump_77 =>
                cases assump_76
                case intro assump_78 assump_79 =>
                  cases assump_79
                  case inl assump_82 =>
                    cases assump_77
                    case inl assump_86 =>
                      have assump_240 : True := by
                        apply True.intro
                      let assump_92 := assump_78 assump_240
                      apply False.elim assump_92
                    case inr assump_87 =>
                      have assump_241 : True := by
                        apply True.intro
                      let assump_100 := assump_78 assump_241
                      apply False.elim assump_100
                  case inr assump_83 =>
                    cases assump_77
                    case inl assump_106 =>
                      have assump_242 : True := by
                        apply True.intro
                      let assump_112 := assump_78 assump_242
                      apply False.elim assump_112
                    case inr assump_107 =>
                      have assump_243 : True := by
                        apply True.intro
                      let assump_120 := assump_78 assump_243
                      apply False.elim assump_120
          case inr assump_67 =>
            cases assump_3
            case intro assump_128 assump_129 =>
              cases assump_129
              case intro assump_132 assump_133 =>
                cases assump_132
                case intro assump_134 assump_135 =>
                  cases assump_135
                  case inl assump_138 =>
                    cases assump_133
                    case inl assump_142 =>
                      have assump_244 : True := by
                        apply True.intro
                      let assump_148 := assump_134 assump_244
                      apply False.elim assump_148
                    case inr assump_143 =>
                      have assump_245 : True := by
                        apply True.intro
                      let assump_156 := assump_134 assump_245
                      apply False.elim assump_156
                  case inr assump_139 =>
                    cases assump_133
                    case inl assump_162 =>
                      have assump_246 : True := by
                        apply True.intro
                      let assump_168 := assump_134 assump_246
                      apply False.elim assump_168
                    case inr assump_163 =>
                      have assump_247 : True := by
                        apply True.intro
                      let assump_176 := assump_134 assump_247
                      apply False.elim assump_176
        case inr assump_65 =>
          cases assump_3
          case intro assump_184 assump_185 =>
            cases assump_185
            case intro assump_188 assump_189 =>
              cases assump_188
              case intro assump_190 assump_191 =>
                cases assump_191
                case inl assump_194 =>
                  cases assump_189
                  case inl assump_198 =>
                    have assump_248 : True := by
                      apply True.intro
                    let assump_204 := assump_190 assump_248
                    apply False.elim assump_204
                  case inr assump_199 =>
                    have assump_249 : True := by
                      apply True.intro
                    let assump_212 := assump_190 assump_249
                    apply False.elim assump_212
                case inr assump_195 =>
                  cases assump_189
                  case inl assump_218 =>
                    have assump_250 : True := by
                      apply True.intro
                    let assump_224 := assump_190 assump_250
                    apply False.elim assump_224
                  case inr assump_219 =>
                    have assump_251 : True := by
                      apply True.intro
                    let assump_232 := assump_190 assump_251
                    apply False.elim assump_232


variable (p7 p0 p6 p3 p1 p4 : Prop)
theorem file4_32219 : ((((((p3 ∨ p0) → (p4 → p0)) → False) ∨ (((p1 ∨ p0) ∨ (p3 → False)) ∧ ((p4 → p0) → False))) ∧ ((((False → p7) ∧ (p6 ∨ p4)) ∨ ((p3 ∧ p3) → (p1 → p3))) → False)) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case inl assump_12 =>
      have assump_110 : (((False → p7) ∧ (p6 ∨ p4)) ∨ ((p3 ∧ p3) → (p1 → p3))) := by
        apply Or.inr
        intro assump_22
        intro assump_23
        cases assump_22
        case intro assump_26 assump_27 =>
          exact assump_27
      let assump_18 := assump_11 assump_110
      apply False.elim assump_18
    case inr assump_13 =>
      cases assump_13
      case intro assump_35 assump_36 =>
        cases assump_35
        case inl assump_37 =>
          cases assump_37
          case inl assump_39 =>
            have assump_111 : (((False → p7) ∧ (p6 ∨ p4)) ∨ ((p3 ∧ p3) → (p1 → p3))) := by
              apply Or.inr
              intro assump_51
              intro assump_52
              cases assump_51
              case intro assump_55 assump_56 =>
                exact assump_56
            let assump_47 := assump_11 assump_111
            apply False.elim assump_47
          case inr assump_40 =>
            have assump_112 : (((False → p7) ∧ (p6 ∨ p4)) ∨ ((p3 ∧ p3) → (p1 → p3))) := by
              apply Or.inr
              intro assump_74
              intro assump_75
              cases assump_74
              case intro assump_78 assump_79 =>
                exact assump_79
            let assump_70 := assump_11 assump_112
            apply False.elim assump_70
        case inr assump_38 =>
          have assump_113 : (((False → p7) ∧ (p6 ∨ p4)) ∨ ((p3 ∧ p3) → (p1 → p3))) := by
            apply Or.inr
            intro assump_97
            intro assump_98
            cases assump_97
            case intro assump_101 assump_102 =>
              exact assump_102
          let assump_93 := assump_11 assump_113
          apply False.elim assump_93


variable (p0 p7 p1 p5 p3 p6 : Prop)
theorem file4_34270 : ((((((p7 ∨ p3) ∨ (p6 ∧ p7)) → False) ∧ (((p5 → False) ∨ (p5 ∨ p0)) ∧ ((p0 → False) ∧ (False ∧ True)))) ∧ ((((p7 ∧ False) ∧ (p1 ∧ True)) ∨ ((p3 → p0) ∨ (p7 → False))) → (((p7 ∨ p5) ∧ (p0 ∧ False)) ∧ ((p6 ∨ False) → (p3 ∨ p3))))) → False) := by
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
            cases assump_15
            case intro assump_18 assump_19 =>
              apply False.elim assump_18
        case inr assump_11 =>
          cases assump_11
          case inl assump_22 =>
            cases assump_9
            case intro assump_26 assump_27 =>
              cases assump_27
              case intro assump_30 assump_31 =>
                apply False.elim assump_30
          case inr assump_23 =>
            cases assump_9
            case intro assump_36 assump_37 =>
              cases assump_37
              case intro assump_40 assump_41 =>
                apply False.elim assump_40


variable (p6 p3 p1 p7 p2 p4 p5 : Prop)
theorem file4_35503 : (((((True ∧ p5) → False) ∧ ((p2 ∧ p5) ∧ (p1 ∧ False))) → False) ∨ ((((p4 ∧ p1) → False) ∧ ((p7 ∧ p6) → False)) ∧ (((p3 → False) ∧ (p3 → p3)) → ((False → p3) → (p4 → p1))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply False.elim assump_15


variable (p3 p4 p5 p1 p2 : Prop)
theorem file4_36038 : ((((((p3 → False) ∧ (False → False)) ∧ ((p2 → p2) ∨ (False ∨ p2))) → False) ∧ ((((p4 → False) ∧ (True → False)) → False) ∧ (((False → False) ∨ (p1 ∧ p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_19 : ((False → False) ∨ (p1 ∧ p5)) := by
        apply Or.inl
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_7 assump_19
      apply False.elim assump_12


variable (p7 p6 p3 p1 p0 : Prop)
theorem file4_36612 : (((((True ∨ p6) → (False → False)) → ((False → False) ∨ (False → p7))) ∨ (((False → p6) ∧ (True → False)) ∨ ((p6 ∧ p7) ∧ (p1 ∨ p0)))) ∨ ((((p1 → False) ∧ (p3 ∧ p7)) → False) ∧ (((True → p0) ∧ (False ∧ p6)) ∧ ((p0 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p1 p6 p7 p4 p5 p2 p3 : Prop)
theorem file4_37022 : (((((p5 ∧ False) → (p2 → False)) → False) → False) ∨ ((((p5 → False) → (p2 ∧ p5)) → False) ∧ (((False ∧ p6) ∧ (p4 ∨ p4)) ∧ ((p7 ∨ p4) → (p3 ∨ p1))))) := by
  apply Or.inl
  intro assump_8
  have assump_25 : ((p5 ∧ False) → (p2 → False)) := by
    intro assump_12
    intro assump_13
    cases assump_12
    case intro assump_16 assump_17 =>
      apply False.elim assump_17
  let assump_11 := assump_8 assump_25
  apply False.elim assump_11


variable (p3 p2 p0 p4 : Prop)
theorem file4_37517 : (((((p0 ∧ False) ∧ (p3 ∧ p3)) ∧ ((True → p3) ∧ (p2 → p2))) → False) ∨ ((((True → False) → False) → False) ∧ (((p3 ∧ False) ∧ (p4 → False)) ∨ ((p2 → True) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_7


variable (p4 p6 p7 p3 : Prop)
theorem file4_37974 : ((((((p7 → False) ∨ (p3 → False)) ∨ ((p3 → False) → (p4 ∧ True))) → (((p3 ∨ True) → False) → ((p6 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p7 → False) ∨ (p3 → False)) ∨ ((p3 → False) → (p4 ∧ True))) → (((p3 ∨ True) → False) → ((p6 ∧ False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p4 p5 p2 p6 p1 p3 p0 : Prop)
theorem file4_38546 : (((((p2 ∧ True) ∨ (p4 → p4)) ∨ ((p0 → False) → False)) ∨ (((p1 ∧ p2) → False) → ((p1 ∨ p6) ∨ (p1 → False)))) ∨ ((((False → False) → False) ∨ ((p4 ∧ p6) → False)) ∧ (((p0 ∨ p5) ∨ (p0 → False)) → ((p3 → False) ∧ (False → p4))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_29
  exact assump_29


variable (p5 p0 p3 p1 p2 p6 p7 : Prop)
theorem file4_38938 : ((((((True ∧ p7) ∨ (p6 → True)) ∨ ((p2 → False) ∨ (p5 → False))) → False) ∨ ((((p0 → p3) ∨ (p1 → False)) → ((p3 ∨ True) ∨ (p6 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_24 : (((True ∧ p7) ∨ (p6 → True)) ∨ ((p2 → False) ∨ (p5 → False))) := by
      apply Or.inl
      apply Or.inr
      intro assump_7
      apply True.intro
    let assump_6 := assump_2 assump_24
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_25 : (((p0 → p3) ∨ (p1 → False)) → ((p3 ∨ True) ∨ (p6 → False))) := by
      intro assump_14
      cases assump_14
      case inl assump_15 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_16 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
    let assump_13 := assump_3 assump_25
    apply False.elim assump_13


variable (p5 p2 p6 p3 p7 p4 p0 p1 : Prop)
theorem file4_39878 : (((((p6 → False) → False) → False) → (((p7 → p3) → (p6 → False)) → False)) → ((((True ∧ False) → (p4 → False)) ∨ ((False ∧ p1) ∧ (p1 ∧ False))) ∨ (((p1 → p2) ∧ (p5 → False)) ∨ ((True → True) → (p2 ∧ p0))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_9


variable (p4 : Prop)
theorem file4_40298 : ((((((True → False) → False) ∧ ((True ∨ p4) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((True → False) → False) ∧ ((True ∨ p4) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_20 : (True ∨ p4) := by
        apply Or.inl
        apply True.intro
      let assump_12 := assump_7 assump_20
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p7 p0 p1 p6 p2 p5 p3 : Prop)
theorem file4_40852 : (((((p7 ∨ p3) → False) ∧ ((True → False) ∧ (p1 → p3))) ∧ (((p7 ∧ p0) → (p1 ∨ p7)) ∧ ((p5 ∧ p2) ∧ (p6 ∧ True)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              cases assump_19
              case intro assump_26 assump_27 =>
                have assump_41 : True := by
                  apply True.intro
                let assump_37 := assump_8 assump_41
                apply False.elim assump_37


variable (p5 p1 p7 p4 p3 p0 p2 : Prop)
theorem file4_41685 : (((((True → False) ∧ (p4 ∨ p3)) → False) → False) → ((((p0 ∨ p0) ∧ (False ∨ p0)) → ((p7 ∨ p4) ∧ (p4 ∨ p1))) ∧ (((p2 → p1) ∧ (p1 ∨ p0)) ∧ ((p3 ∧ p5) ∧ (p5 ∨ True))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case inl assump_9 =>
        apply False.elim assump_9
      case inr assump_10 =>
        have assump_264 : (((True → False) ∧ (p4 ∨ p3)) → False) := by
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            cases assump_20
            case inl assump_23 =>
              have assump_265 : True := by
                apply True.intro
              let assump_28 := assump_19 assump_265
              apply False.elim assump_28
            case inr assump_24 =>
              have assump_266 : True := by
                apply True.intro
              let assump_35 := assump_19 assump_266
              apply False.elim assump_35
        let assump_17 := assump_1 assump_264
        apply False.elim assump_17
    case inr assump_6 =>
      cases assump_4
      case inl assump_44 =>
        apply False.elim assump_44
      case inr assump_45 =>
        have assump_267 : (((True → False) ∧ (p4 ∨ p3)) → False) := by
          intro assump_53
          cases assump_53
          case intro assump_54 assump_55 =>
            cases assump_55
            case inl assump_58 =>
              have assump_268 : True := by
                apply True.intro
              let assump_63 := assump_54 assump_268
              apply False.elim assump_63
            case inr assump_59 =>
              have assump_269 : True := by
                apply True.intro
              let assump_70 := assump_54 assump_269
              apply False.elim assump_70
        let assump_52 := assump_1 assump_267
        apply False.elim assump_52
  cases assump_2
  case intro assump_77 assump_78 =>
    cases assump_77
    case inl assump_79 =>
      cases assump_78
      case inl assump_83 =>
        apply False.elim assump_83
      case inr assump_84 =>
        have assump_270 : (((True → False) ∧ (p4 ∨ p3)) → False) := by
          intro assump_92
          cases assump_92
          case intro assump_93 assump_94 =>
            cases assump_94
            case inl assump_97 =>
              have assump_271 : True := by
                apply True.intro
              let assump_102 := assump_93 assump_271
              apply False.elim assump_102
            case inr assump_98 =>
              have assump_272 : True := by
                apply True.intro
              let assump_109 := assump_93 assump_272
              apply False.elim assump_109
        let assump_91 := assump_1 assump_270
        apply False.elim assump_91
    case inr assump_80 =>
      cases assump_78
      case inl assump_118 =>
        apply False.elim assump_118
      case inr assump_119 =>
        have assump_273 : (((True → False) ∧ (p4 ∨ p3)) → False) := by
          intro assump_127
          cases assump_127
          case intro assump_128 assump_129 =>
            cases assump_129
            case inl assump_132 =>
              have assump_274 : True := by
                apply True.intro
              let assump_137 := assump_128 assump_274
              apply False.elim assump_137
            case inr assump_133 =>
              have assump_275 : True := by
                apply True.intro
              let assump_144 := assump_128 assump_275
              apply False.elim assump_144
        let assump_126 := assump_1 assump_273
        apply False.elim assump_126
  apply And.intro
  apply And.intro
  intro assump_151
  have assump_276 : (((True → False) ∧ (p4 ∨ p3)) → False) := by
    intro assump_157
    cases assump_157
    case intro assump_158 assump_159 =>
      cases assump_159
      case inl assump_162 =>
        have assump_277 : True := by
          apply True.intro
        let assump_167 := assump_158 assump_277
        apply False.elim assump_167
      case inr assump_163 =>
        have assump_278 : True := by
          apply True.intro
        let assump_174 := assump_158 assump_278
        apply False.elim assump_174
  let assump_156 := assump_1 assump_276
  apply False.elim assump_156
  have assump_279 : (((True → False) ∧ (p4 ∨ p3)) → False) := by
    intro assump_184
    cases assump_184
    case intro assump_185 assump_186 =>
      cases assump_186
      case inl assump_189 =>
        have assump_280 : True := by
          apply True.intro
        let assump_194 := assump_185 assump_280
        apply False.elim assump_194
      case inr assump_190 =>
        have assump_281 : True := by
          apply True.intro
        let assump_201 := assump_185 assump_281
        apply False.elim assump_201
  let assump_183 := assump_1 assump_279
  apply False.elim assump_183
  apply And.intro
  apply And.intro
  have assump_282 : (((True → False) ∧ (p4 ∨ p3)) → False) := by
    intro assump_211
    cases assump_211
    case intro assump_212 assump_213 =>
      cases assump_213
      case inl assump_216 =>
        have assump_283 : True := by
          apply True.intro
        let assump_221 := assump_212 assump_283
        apply False.elim assump_221
      case inr assump_217 =>
        have assump_284 : True := by
          apply True.intro
        let assump_228 := assump_212 assump_284
        apply False.elim assump_228
  let assump_210 := assump_1 assump_282
  apply False.elim assump_210
  have assump_285 : (((True → False) ∧ (p4 ∨ p3)) → False) := by
    intro assump_238
    cases assump_238
    case intro assump_239 assump_240 =>
      cases assump_240
      case inl assump_243 =>
        have assump_286 : True := by
          apply True.intro
        let assump_248 := assump_239 assump_286
        apply False.elim assump_248
      case inr assump_244 =>
        have assump_287 : True := by
          apply True.intro
        let assump_255 := assump_239 assump_287
        apply False.elim assump_255
  let assump_237 := assump_1 assump_285
  apply False.elim assump_237
  apply Or.inr
  apply True.intro


variable (p6 p0 p4 p3 p7 p1 p5 : Prop)
theorem file4_47930 : (((((p3 ∧ p7) ∨ (p7 → False)) → ((p4 → False) → (False → p5))) ∨ (((p5 → p5) → False) → False)) ∨ ((((p4 ∧ p1) → (p6 → p3)) ∧ ((False → False) → (p4 ∧ p4))) → (((p7 → False) → (False ∨ p3)) → ((True → p1) ∨ (p0 ∧ p0))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply False.elim assump_3


variable (p2 p6 p0 p4 p7 p3 p1 p5 : Prop)
theorem file4_48332 : (((((False → False) ∨ (p4 ∧ p1)) ∨ ((p0 ∧ p6) → (p6 ∨ p3))) ∨ (((p4 ∨ False) → False) → ((p2 ∨ p7) ∨ (p5 → False)))) ∨ ((((p1 → p6) → (p4 → False)) ∧ ((p6 ∨ p3) ∧ (p7 ∧ p7))) ∨ (((p3 ∧ True) → False) ∧ ((True ∨ p2) ∨ (p0 ∨ p4))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p6 p5 p2 p1 p4 p3 p7 p0 : Prop)
theorem file4_48740 : (((((False → False) ∨ (False ∧ p6)) → False) ∧ (((True ∨ p5) ∨ (p7 → False)) ∧ ((p4 ∨ p3) ∧ (p5 → p1)))) → ((((p5 → p2) ∧ (True ∧ False)) ∨ ((p0 ∨ False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
  case inr assump_4 =>
    cases assump_1
    case intro assump_17 assump_18 =>
      cases assump_18
      case intro assump_21 assump_22 =>
        cases assump_21
        case inl assump_23 =>
          cases assump_23
          case inl assump_25 =>
            cases assump_22
            case intro assump_29 assump_30 =>
              cases assump_29
              case inl assump_31 =>
                have assump_129 : ((False → False) ∨ (False ∧ p6)) := by
                  apply Or.inl
                  intro assump_40
                  apply False.elim assump_40
                let assump_39 := assump_17 assump_129
                apply False.elim assump_39
              case inr assump_32 =>
                have assump_130 : ((False → False) ∨ (False ∧ p6)) := by
                  apply Or.inl
                  intro assump_53
                  apply False.elim assump_53
                let assump_52 := assump_17 assump_130
                apply False.elim assump_52
          case inr assump_26 =>
            cases assump_22
            case intro assump_61 assump_62 =>
              cases assump_61
              case inl assump_63 =>
                have assump_131 : ((False → False) ∨ (False ∧ p6)) := by
                  apply Or.inl
                  intro assump_74
                  apply False.elim assump_74
                let assump_73 := assump_17 assump_131
                apply False.elim assump_73
              case inr assump_64 =>
                have assump_132 : ((False → False) ∨ (False ∧ p6)) := by
                  apply Or.inl
                  intro assump_89
                  apply False.elim assump_89
                let assump_88 := assump_17 assump_132
                apply False.elim assump_88
        case inr assump_24 =>
          cases assump_22
          case intro assump_97 assump_98 =>
            cases assump_97
            case inl assump_99 =>
              have assump_133 : ((False → False) ∨ (False ∧ p6)) := by
                apply Or.inl
                intro assump_109
                apply False.elim assump_109
              let assump_108 := assump_17 assump_133
              apply False.elim assump_108
            case inr assump_100 =>
              have assump_134 : ((False → False) ∨ (False ∧ p6)) := by
                apply Or.inl
                intro assump_123
                apply False.elim assump_123
              let assump_122 := assump_17 assump_134
              apply False.elim assump_122


variable (p0 p1 p6 p4 p5 p2 : Prop)
theorem file4_51703 : ((((((p1 ∨ p4) ∨ (p6 → False)) ∧ ((True → False) ∧ (p2 → False))) → (((p6 ∧ p2) → (p5 → p0)) ∧ ((p4 → True) → (p5 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_156 : ((((p1 ∨ p4) ∨ (p6 → False)) ∧ ((True → False) ∧ (p2 → False))) → (((p6 ∧ p2) → (p5 → p0)) ∧ ((p4 → True) → (p5 ∧ p0)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_5
      case intro assump_16 assump_17 =>
        cases assump_16
        case inl assump_18 =>
          cases assump_18
          case inl assump_20 =>
            cases assump_17
            case intro assump_24 assump_25 =>
              have assump_157 : p2 := by
                exact assump_11
              let assump_30 := assump_25 assump_157
              apply False.elim assump_30
          case inr assump_21 =>
            cases assump_17
            case intro assump_36 assump_37 =>
              have assump_158 : p2 := by
                exact assump_11
              let assump_42 := assump_37 assump_158
              apply False.elim assump_42
        case inr assump_19 =>
          cases assump_17
          case intro assump_48 assump_49 =>
            have assump_159 : p2 := by
              exact assump_11
            let assump_54 := assump_49 assump_159
            apply False.elim assump_54
    intro assump_58
    apply And.intro
    cases assump_5
    case intro assump_61 assump_62 =>
      cases assump_61
      case inl assump_63 =>
        cases assump_63
        case inl assump_65 =>
          cases assump_62
          case intro assump_69 assump_70 =>
            have assump_160 : True := by
              apply True.intro
            let assump_76 := assump_69 assump_160
            apply False.elim assump_76
        case inr assump_66 =>
          cases assump_62
          case intro assump_82 assump_83 =>
            have assump_161 : True := by
              apply True.intro
            let assump_89 := assump_82 assump_161
            apply False.elim assump_89
      case inr assump_64 =>
        cases assump_62
        case intro assump_95 assump_96 =>
          have assump_162 : True := by
            apply True.intro
          let assump_102 := assump_95 assump_162
          apply False.elim assump_102
    cases assump_5
    case intro assump_108 assump_109 =>
      cases assump_108
      case inl assump_110 =>
        cases assump_110
        case inl assump_112 =>
          cases assump_109
          case intro assump_116 assump_117 =>
            have assump_163 : True := by
              apply True.intro
            let assump_123 := assump_116 assump_163
            apply False.elim assump_123
        case inr assump_113 =>
          cases assump_109
          case intro assump_129 assump_130 =>
            have assump_164 : True := by
              apply True.intro
            let assump_136 := assump_129 assump_164
            apply False.elim assump_136
      case inr assump_111 =>
        cases assump_109
        case intro assump_142 assump_143 =>
          have assump_165 : True := by
            apply True.intro
          let assump_149 := assump_142 assump_165
          apply False.elim assump_149
  let assump_4 := assump_1 assump_156
  apply False.elim assump_4


variable (p4 p1 p3 : Prop)
theorem file4_55076 : (((((False → False) → False) ∧ ((p1 ∨ p3) → False)) ∨ (((False → False) ∨ (p4 ∨ False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_27 : (False → False) := by
        intro assump_12
        apply False.elim assump_12
      let assump_11 := assump_4 assump_27
      apply False.elim assump_11
  case inr assump_3 =>
    have assump_28 : ((False → False) ∨ (p4 ∨ False)) := by
      apply Or.inl
      intro assump_21
      apply False.elim assump_21
    let assump_20 := assump_3 assump_28
    apply False.elim assump_20


variable (p1 p7 p6 p0 p5 p4 p3 : Prop)
theorem file4_55771 : ((((((p0 ∧ p1) → False) ∧ ((True ∨ p1) → False)) → (((p5 ∧ p7) → False) ∧ ((p5 ∧ p6) → False))) ∧ ((((p4 → False) → (True ∨ p4)) ∨ ((p4 ∧ p5) ∨ (p6 ∨ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((p4 → False) → (True ∨ p4)) ∨ ((p4 ∧ p5) ∨ (p6 ∨ p3))) := by
      apply Or.inl
      intro assump_9
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p6 p2 p7 p1 p4 : Prop)
theorem file4_56312 : ((((((False → p7) → False) → False) ∧ (((False ∧ p1) → False) ∨ ((p2 → p4) ∧ (p6 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((False → p7) → False) → False) ∧ (((False ∧ p1) → False) ∨ ((p2 → p4) ∧ (p6 ∨ p6)))) := by
    apply And.intro
    intro assump_5
    have assump_24 : (False → p7) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_24
    apply False.elim assump_8
    apply Or.inl
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p2 p0 p3 : Prop)
theorem file4_57001 : ((((((p3 ∧ p2) ∧ (p2 → False)) ∧ ((p0 → p3) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p3 ∧ p2) ∧ (p2 → False)) ∧ ((p0 → p3) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_31 : (p0 → p3) := by
            intro assump_21
            exact assump_10
          let assump_20 := assump_7 assump_31
          apply False.elim assump_20
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p2 p7 p1 p0 p5 p3 p6 : Prop)
theorem file4_57699 : ((((((p6 ∧ False) ∧ (p2 → False)) → ((p1 ∧ p0) ∧ (p7 → False))) → False) ∧ ((((False → False) → False) ∨ ((p1 ∧ p2) → (p2 → p6))) ∨ (((True ∨ p5) ∨ (p6 → False)) ∧ ((p3 ∧ p7) ∨ (p1 ∧ p6))))) → False) := by
  intro assump_71
  cases assump_71
  case intro assump_72 assump_73 =>
    cases assump_73
    case inl assump_76 =>
      cases assump_76
      case inl assump_78 =>
        have assump_357 : (False → False) := by
          intro assump_83
          apply False.elim assump_83
        let assump_82 := assump_78 assump_357
        apply False.elim assump_82
      case inr assump_79 =>
        have assump_358 : (((p6 ∧ False) ∧ (p2 → False)) → ((p1 ∧ p0) ∧ (p7 → False))) := by
          intro assump_93
          apply And.intro
          apply And.intro
          cases assump_93
          case intro assump_94 assump_95 =>
            cases assump_94
            case intro assump_96 assump_97 =>
              apply False.elim assump_97
          cases assump_93
          case intro assump_102 assump_103 =>
            cases assump_102
            case intro assump_104 assump_105 =>
              apply False.elim assump_105
          intro assump_110
          cases assump_93
          case intro assump_113 assump_114 =>
            cases assump_113
            case intro assump_115 assump_116 =>
              apply False.elim assump_116
        let assump_92 := assump_72 assump_358
        apply False.elim assump_92
    case inr assump_77 =>
      cases assump_77
      case intro assump_124 assump_125 =>
        cases assump_124
        case inl assump_126 =>
          cases assump_126
          case inl assump_128 =>
            cases assump_125
            case inl assump_132 =>
              cases assump_132
              case intro assump_134 assump_135 =>
                have assump_359 : (((p6 ∧ False) ∧ (p2 → False)) → ((p1 ∧ p0) ∧ (p7 → False))) := by
                  intro assump_143
                  apply And.intro
                  apply And.intro
                  cases assump_143
                  case intro assump_144 assump_145 =>
                    cases assump_144
                    case intro assump_146 assump_147 =>
                      apply False.elim assump_147
                  cases assump_143
                  case intro assump_152 assump_153 =>
                    cases assump_152
                    case intro assump_154 assump_155 =>
                      apply False.elim assump_155
                  intro assump_160
                  cases assump_143
                  case intro assump_163 assump_164 =>
                    cases assump_163
                    case intro assump_165 assump_166 =>
                      apply False.elim assump_166
                let assump_142 := assump_72 assump_359
                apply False.elim assump_142
            case inr assump_133 =>
              cases assump_133
              case intro assump_174 assump_175 =>
                have assump_360 : (((p6 ∧ False) ∧ (p2 → False)) → ((p1 ∧ p0) ∧ (p7 → False))) := by
                  intro assump_183
                  apply And.intro
                  apply And.intro
                  cases assump_183
                  case intro assump_184 assump_185 =>
                    cases assump_184
                    case intro assump_186 assump_187 =>
                      apply False.elim assump_187
                  cases assump_183
                  case intro assump_192 assump_193 =>
                    cases assump_192
                    case intro assump_194 assump_195 =>
                      apply False.elim assump_195
                  intro assump_200
                  cases assump_183
                  case intro assump_203 assump_204 =>
                    cases assump_203
                    case intro assump_205 assump_206 =>
                      apply False.elim assump_206
                let assump_182 := assump_72 assump_360
                apply False.elim assump_182
          case inr assump_129 =>
            cases assump_125
            case inl assump_216 =>
              cases assump_216
              case intro assump_218 assump_219 =>
                have assump_361 : (((p6 ∧ False) ∧ (p2 → False)) → ((p1 ∧ p0) ∧ (p7 → False))) := by
                  intro assump_228
                  apply And.intro
                  apply And.intro
                  cases assump_228
                  case intro assump_229 assump_230 =>
                    cases assump_229
                    case intro assump_231 assump_232 =>
                      apply False.elim assump_232
                  cases assump_228
                  case intro assump_237 assump_238 =>
                    cases assump_237
                    case intro assump_239 assump_240 =>
                      apply False.elim assump_240
                  intro assump_245
                  cases assump_228
                  case intro assump_248 assump_249 =>
                    cases assump_248
                    case intro assump_250 assump_251 =>
                      apply False.elim assump_251
                let assump_227 := assump_72 assump_361
                apply False.elim assump_227
            case inr assump_217 =>
              cases assump_217
              case intro assump_259 assump_260 =>
                have assump_362 : (((p6 ∧ False) ∧ (p2 → False)) → ((p1 ∧ p0) ∧ (p7 → False))) := by
                  intro assump_269
                  apply And.intro
                  apply And.intro
                  cases assump_269
                  case intro assump_270 assump_271 =>
                    cases assump_270
                    case intro assump_272 assump_273 =>
                      apply False.elim assump_273
                  cases assump_269
                  case intro assump_278 assump_279 =>
                    cases assump_278
                    case intro assump_280 assump_281 =>
                      apply False.elim assump_281
                  intro assump_286
                  cases assump_269
                  case intro assump_289 assump_290 =>
                    cases assump_289
                    case intro assump_291 assump_292 =>
                      apply False.elim assump_292
                let assump_268 := assump_72 assump_362
                apply False.elim assump_268
        case inr assump_127 =>
          cases assump_125
          case inl assump_302 =>
            cases assump_302
            case intro assump_304 assump_305 =>
              have assump_363 : (((p6 ∧ False) ∧ (p2 → False)) → ((p1 ∧ p0) ∧ (p7 → False))) := by
                intro assump_314
                apply And.intro
                apply And.intro
                cases assump_314
                case intro assump_315 assump_316 =>
                  cases assump_315
                  case intro assump_317 assump_318 =>
                    apply False.elim assump_318
                cases assump_314
                case intro assump_323 assump_324 =>
                  cases assump_323
                  case intro assump_325 assump_326 =>
                    apply False.elim assump_326
                intro assump_331
                cases assump_314
                case intro assump_334 assump_335 =>
                  cases assump_334
                  case intro assump_336 assump_337 =>
                    apply False.elim assump_337
              let assump_313 := assump_72 assump_363
              apply False.elim assump_313
          case inr assump_303 =>
            cases assump_303
            case intro assump_345 assump_346 =>
              have assump_364 : p6 := by
                exact assump_346
              let assump_353 := assump_127 assump_364
              apply False.elim assump_353


variable (p5 p0 p1 p3 p4 : Prop)
theorem file4_65531 : (((((False → False) ∨ (False → False)) → False) → False) ∨ ((((False ∧ p1) → False) → ((p5 → True) ∨ (p1 ∨ p0))) → (((p4 ∨ True) → (p3 ∧ False)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False → False) ∨ (False → False)) := by
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p5 p6 p3 p0 p7 p2 : Prop)
theorem file4_65980 : (((((p4 ∧ False) → (p4 → False)) → False) → (((p2 ∨ p5) ∧ (p2 → False)) ∧ ((p2 ∨ p7) → False))) ∨ ((((p0 ∧ p4) ∨ (p0 ∧ p5)) → ((p7 ∨ p5) ∨ (p3 → p4))) ∧ (((True → False) ∧ (True ∨ p5)) ∨ ((p4 ∧ p6) ∧ (False ∧ False))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  have assump_76 : ((p4 ∧ False) → (p4 → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_76
  apply False.elim assump_4
  intro assump_18
  have assump_77 : ((p4 ∧ False) → (p4 → False)) := by
    intro assump_24
    intro assump_25
    cases assump_24
    case intro assump_28 assump_29 =>
      apply False.elim assump_29
  let assump_23 := assump_1 assump_77
  apply False.elim assump_23
  intro assump_37
  cases assump_37
  case inl assump_38 =>
    have assump_78 : ((p4 ∧ False) → (p4 → False)) := by
      intro assump_45
      intro assump_46
      cases assump_45
      case intro assump_49 assump_50 =>
        apply False.elim assump_50
    let assump_44 := assump_1 assump_78
    apply False.elim assump_44
  case inr assump_39 =>
    have assump_79 : ((p4 ∧ False) → (p4 → False)) := by
      intro assump_63
      intro assump_64
      cases assump_63
      case intro assump_67 assump_68 =>
        apply False.elim assump_68
    let assump_62 := assump_1 assump_79
    apply False.elim assump_62


variable (p4 p3 p1 p6 : Prop)
theorem file4_67468 : (((((p3 → p1) → False) ∨ ((p6 → p3) ∨ (False ∧ p1))) ∧ (((p4 ∧ True) → (p4 ∧ p4)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_54 : ((p4 ∧ True) → (p4 ∧ p4)) := by
        intro assump_11
        apply And.intro
        cases assump_11
        case intro assump_12 assump_13 =>
          exact assump_12
        cases assump_11
        case intro assump_18 assump_19 =>
          exact assump_18
      let assump_10 := assump_3 assump_54
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_27 =>
        have assump_55 : ((p4 ∧ True) → (p4 ∧ p4)) := by
          intro assump_34
          apply And.intro
          cases assump_34
          case intro assump_35 assump_36 =>
            exact assump_35
          cases assump_34
          case intro assump_41 assump_42 =>
            exact assump_41
        let assump_33 := assump_3 assump_55
        apply False.elim assump_33
      case inr assump_28 =>
        cases assump_28
        case intro assump_50 assump_51 =>
          apply False.elim assump_50


variable (p6 p1 p7 : Prop)
theorem file4_68689 : (((((True ∧ False) → (p7 → p6)) ∧ ((True ∧ p1) ∨ (True ∨ p6))) → False) → False) := by
  intro assump_1
  have assump_18 : (((True ∧ False) → (p7 → p6)) ∧ ((True ∧ p1) ∨ (True ∨ p6))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p2 p4 p5 p6 p1 p0 p3 : Prop)
theorem file4_69212 : (((((p3 → p1) → (p4 → False)) ∨ ((p6 ∨ p4) ∧ (p5 → p5))) → (((p1 ∧ p1) → (p3 ∨ p3)) ∧ ((False ∨ False) ∨ (p0 → p6)))) → ((((p7 ∨ p3) ∧ (p5 → p0)) ∨ ((True → False) → False)) ∨ (((p2 ∧ p2) → False) → ((p3 → False) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  have assump_11 : True := by
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p4 p3 p2 p7 p1 : Prop)
theorem file4_69680 : (((((p4 → False) → (p3 ∧ p2)) ∧ ((p1 → False) → False)) ∧ (((False ∧ p7) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_21 : ((False ∧ p7) → False) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
      let assump_12 := assump_3 assump_21
      apply False.elim assump_12


variable (p0 p5 p7 p1 p6 p4 p2 : Prop)
theorem file4_70227 : ((((((p7 ∨ p6) → False) ∧ ((p7 ∨ p7) ∨ (p0 ∧ p0))) → False) ∧ ((((p7 ∨ True) ∧ (p1 → False)) ∧ ((False ∧ p5) ∧ (p5 → p2))) ∧ (((p1 → p7) → (p4 → False)) ∨ ((p0 ∨ p6) ∨ (p1 ∨ p7))))) → False) := by
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
          case inl assump_12 =>
            cases assump_9
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                apply False.elim assump_20
          case inr assump_13 =>
            cases assump_9
            case intro assump_28 assump_29 =>
              cases assump_28
              case intro assump_30 assump_31 =>
                apply False.elim assump_30


variable (p5 p6 p4 p1 p0 p7 : Prop)
theorem file4_71209 : (((((True → False) ∨ (p4 ∧ False)) → ((p4 → False) ∨ (p6 ∧ False))) → False) → ((((True ∧ True) → False) ∧ ((p0 → False) ∨ (p0 ∨ False))) ∨ (((p5 → False) ∧ (True → p1)) → ((p1 → False) ∧ (p5 → p7))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_61 : (((True → False) ∨ (p4 ∧ False)) → ((p4 → False) ∨ (p6 ∧ False))) := by
      intro assump_12
      cases assump_12
      case inl assump_13 =>
        apply Or.inl
        intro assump_17
        have assump_62 : True := by
          apply True.intro
        let assump_21 := assump_13 assump_62
        apply False.elim assump_21
      case inr assump_14 =>
        cases assump_14
        case intro assump_25 assump_26 =>
          apply False.elim assump_26
    let assump_11 := assump_1 assump_61
    apply False.elim assump_11
  apply Or.inl
  intro assump_34
  have assump_63 : (((True → False) ∨ (p4 ∧ False)) → ((p4 → False) ∨ (p6 ∧ False))) := by
    intro assump_39
    cases assump_39
    case inl assump_40 =>
      apply Or.inl
      intro assump_44
      have assump_64 : True := by
        apply True.intro
      let assump_48 := assump_40 assump_64
      apply False.elim assump_48
    case inr assump_41 =>
      cases assump_41
      case intro assump_52 assump_53 =>
        apply False.elim assump_53
  let assump_38 := assump_1 assump_63
  apply False.elim assump_38


variable (p1 p5 p6 p2 : Prop)
theorem file4_72700 : (((((p2 → False) ∧ (p5 → p6)) ∨ ((p5 ∧ p5) ∨ (p6 → False))) → (((False → p6) → (True → False)) → False)) ∨ ((((p1 ∧ p2) ∨ (p2 → False)) → ((p1 ∧ p6) → False)) → (((p6 → p1) ∧ (p1 ∧ p6)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      have assump_52 : (False → p6) := by
        intro assump_16
        apply False.elim assump_16
      let assump_15 := assump_2 assump_52
      have assump_53 : True := by
        apply True.intro
      let assump_19 := assump_15 assump_53
      apply False.elim assump_19
  case inr assump_6 =>
    cases assump_6
    case inl assump_23 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        have assump_54 : (False → p6) := by
          intro assump_34
          apply False.elim assump_34
        let assump_33 := assump_2 assump_54
        have assump_55 : True := by
          apply True.intro
        let assump_37 := assump_33 assump_55
        apply False.elim assump_37
    case inr assump_24 =>
      have assump_56 : (False → p6) := by
        intro assump_45
        apply False.elim assump_45
      let assump_44 := assump_2 assump_56
      have assump_57 : True := by
        apply True.intro
      let assump_48 := assump_44 assump_57
      apply False.elim assump_48


variable (p5 p2 p4 p0 p1 p6 p7 : Prop)
theorem file4_74116 : ((((((p2 → p1) ∨ (False ∨ True)) → ((p6 → False) → False)) ∨ (((p4 ∧ False) ∧ (p2 → p4)) ∨ ((p7 → False) ∨ (p5 → False)))) ∧ ((((p0 ∧ True) ∧ (p6 ∧ False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_87 : (((p0 ∧ True) ∧ (p6 ∧ False)) → False) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_13
            case intro assump_20 assump_21 =>
              apply False.elim assump_21
      let assump_10 := assump_3 assump_87
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_29 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          cases assump_31
          case intro assump_33 assump_34 =>
            apply False.elim assump_34
      case inr assump_30 =>
        cases assump_30
        case inl assump_39 =>
          have assump_88 : (((p0 ∧ True) ∧ (p6 ∧ False)) → False) := by
            intro assump_46
            cases assump_46
            case intro assump_47 assump_48 =>
              cases assump_47
              case intro assump_49 assump_50 =>
                cases assump_48
                case intro assump_55 assump_56 =>
                  apply False.elim assump_56
          let assump_45 := assump_3 assump_88
          apply False.elim assump_45
        case inr assump_40 =>
          have assump_89 : (((p0 ∧ True) ∧ (p6 ∧ False)) → False) := by
            intro assump_69
            cases assump_69
            case intro assump_70 assump_71 =>
              cases assump_70
              case intro assump_72 assump_73 =>
                cases assump_71
                case intro assump_78 assump_79 =>
                  apply False.elim assump_79
          let assump_68 := assump_3 assump_89
          apply False.elim assump_68


variable (p2 p0 p7 p3 p5 p1 : Prop)
theorem file4_76181 : ((((((False ∨ p2) ∧ (True → False)) ∨ ((p1 ∧ p2) → False)) → False) ∧ ((((p5 → p0) ∨ (p7 → p2)) ∧ ((False → False) → False)) ∧ (((p3 → False) ∧ (p1 → True)) ∨ ((False ∧ p1) ∧ (True ∨ p3))))) → False) := by
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
          case inl assump_16 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              have assump_66 : (False → False) := by
                intro assump_27
                apply False.elim assump_27
              let assump_26 := assump_9 assump_66
              apply False.elim assump_26
          case inr assump_17 =>
            cases assump_17
            case intro assump_33 assump_34 =>
              cases assump_33
              case intro assump_35 assump_36 =>
                apply False.elim assump_35
        case inr assump_11 =>
          cases assump_7
          case inl assump_43 =>
            cases assump_43
            case intro assump_45 assump_46 =>
              have assump_67 : (False → False) := by
                intro assump_54
                apply False.elim assump_54
              let assump_53 := assump_9 assump_67
              apply False.elim assump_53
          case inr assump_44 =>
            cases assump_44
            case intro assump_60 assump_61 =>
              cases assump_60
              case intro assump_62 assump_63 =>
                apply False.elim assump_62


variable (p6 p2 p7 p1 p3 p0 : Prop)
theorem file4_77866 : ((((((p6 → False) ∨ (p1 → False)) → ((False → False) ∨ (p2 → False))) ∨ (((True ∧ p3) ∧ (p0 → p6)) → ((p1 → p7) → (p7 ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p6 → False) ∨ (p1 → False)) → ((False → False) ∨ (p2 → False))) ∨ (((True ∧ p3) ∧ (p0 → p6)) → ((p1 → p7) → (p7 ∨ p2)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      apply False.elim assump_10
    case inr assump_7 =>
      apply Or.inl
      intro assump_15
      apply False.elim assump_15
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p7 p6 p3 p0 p5 p1 : Prop)
theorem file4_78562 : (((((p7 → p0) ∧ (False ∧ p0)) → ((p6 ∨ False) ∧ (p5 → False))) ∧ (((p1 → True) → False) → False)) ∧ ((((p0 ∨ p5) → False) ∧ ((True ∧ p3) ∧ (p3 → False))) → False)) := by
  apply And.intro
  apply And.intro
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  intro assump_10
  cases assump_1
  case intro assump_13 assump_14 =>
    cases assump_14
    case intro assump_17 assump_18 =>
      apply False.elim assump_17
  intro assump_21
  have assump_48 : (p1 → True) := by
    intro assump_25
    apply True.intro
  let assump_24 := assump_21 assump_48
  apply False.elim assump_24
  intro assump_29
  cases assump_29
  case intro assump_30 assump_31 =>
    cases assump_31
    case intro assump_34 assump_35 =>
      cases assump_34
      case intro assump_36 assump_37 =>
        have assump_49 : p3 := by
          exact assump_37
        let assump_44 := assump_35 assump_49
        apply False.elim assump_44


variable (p7 p5 p3 p0 p6 p4 p1 : Prop)
theorem file4_79662 : ((((((False ∧ p6) ∨ (p0 → False)) → False) → (((False → p3) ∨ (p5 ∨ p4)) ∨ ((False → p1) ∨ (p7 → p6)))) → False) → False) := by
  intro assump_10
  have assump_23 : ((((False ∧ p6) ∨ (p0 → False)) → False) → (((False → p3) ∨ (p5 ∨ p4)) ∨ ((False → p1) ∨ (p7 → p6)))) := by
    intro assump_14
    apply Or.inl
    apply Or.inl
    intro assump_17
    apply False.elim assump_17
  let assump_13 := assump_10 assump_23
  apply False.elim assump_13


variable (p2 p5 p1 p4 p3 : Prop)
theorem file4_80165 : (((((p1 ∨ False) ∧ (p5 → p2)) ∧ ((True ∧ False) ∨ (p1 → False))) → (((p3 → False) ∧ (p4 ∧ p1)) → False)) ∧ ((((False → False) ∨ (p4 → False)) → False) → False)) := by
  apply And.intro
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_8
    case intro assump_11 assump_12 =>
      cases assump_5
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          cases assump_19
          case inl assump_21 =>
            cases assump_18
            case inl assump_27 =>
              cases assump_27
              case intro assump_29 assump_30 =>
                apply False.elim assump_30
            case inr assump_28 =>
              have assump_53 : p1 := by
                exact assump_21
              let assump_37 := assump_28 assump_53
              apply False.elim assump_37
          case inr assump_22 =>
            apply False.elim assump_22
  intro assump_43
  have assump_54 : ((False → False) ∨ (p4 → False)) := by
    apply Or.inl
    intro assump_47
    apply False.elim assump_47
  let assump_46 := assump_43 assump_54
  apply False.elim assump_46


variable (p4 p7 p2 : Prop)
theorem file4_81392 : (((((p2 → True) → False) → ((p7 ∨ p4) → (p4 ∨ p2))) → False) → False) := by
  intro assump_1
  have assump_25 : (((p2 → True) → False) → ((p7 ∨ p4) → (p4 ∨ p2))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_26 : (p2 → True) := by
        intro assump_14
        apply True.intro
      let assump_13 := assump_5 assump_26
      apply False.elim assump_13
    case inr assump_8 =>
      apply Or.inl
      exact assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p5 p2 p3 p4 p7 p0 p6 : Prop)
theorem file4_82000 : (((((True → False) ∨ (p2 → False)) → ((p5 ∧ p2) ∨ (p0 → p0))) ∨ (((True → False) ∨ (p6 → p7)) → False)) ∨ ((((p6 ∨ p6) ∨ (p6 ∨ p3)) → False) ∨ (((p4 ∨ p4) ∧ (p3 → False)) ∧ ((False → False) ∧ (p3 → p6))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inr
    intro assump_6
    exact assump_6
  case inr assump_3 =>
    apply Or.inr
    intro assump_11
    exact assump_11


variable (p1 p2 p4 p3 p6 p7 : Prop)
theorem file4_82494 : (((((p2 ∧ False) ∧ (p4 → False)) → ((p6 ∨ p1) → (True ∨ False))) ∨ (((p2 ∨ p3) → False) → False)) ∨ ((((p2 → False) ∨ (p6 → p4)) → False) → (((False ∧ p7) ∨ (p2 ∧ p3)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
  case inr assump_4 =>
    cases assump_1
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        apply False.elim assump_20


variable (p4 p5 p3 p0 p7 p1 p6 : Prop)
theorem file4_83173 : (((((p3 ∧ True) ∧ (p5 → False)) ∨ ((True → False) → (p1 ∧ p6))) ∨ (((p7 → p3) → False) → ((p6 → p4) ∧ (p6 → False)))) ∨ ((((p0 ∧ p3) → (p1 → False)) ∧ ((False ∨ p4) ∨ (False → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  apply And.intro
  have assump_14 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4
  have assump_15 : True := by
    apply True.intro
  let assump_10 := assump_1 assump_15
  apply False.elim assump_10


variable (p2 p0 p6 p4 p1 p7 p3 : Prop)
theorem file4_83751 : (((((p0 → False) ∧ (p2 ∨ p7)) ∧ ((p2 ∧ p0) → (p3 ∨ p7))) → False) → ((((p0 ∧ True) → (p4 → True)) ∨ ((p4 → False) ∧ (p1 ∨ p7))) ∨ (((p6 ∨ p4) ∨ (False ∧ p6)) ∧ ((False ∧ p4) → (False ∨ p4))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  apply True.intro


variable (p0 p1 p5 p6 p3 : Prop)
theorem file4_84107 : ((((((p0 → False) → False) ∧ ((True → False) ∨ (p1 → p1))) → (((p6 → p6) ∨ (False ∨ p5)) ∨ ((False ∨ p0) ∧ (p3 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p0 → False) → False) ∧ ((True → False) ∨ (p1 → p1))) → (((p6 → p6) ∨ (False ∨ p5)) ∨ ((False ∨ p0) ∧ (p3 ∨ p6)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inl
        apply Or.inl
        intro assump_14
        exact assump_14
      case inr assump_11 =>
        apply Or.inl
        apply Or.inl
        intro assump_19
        exact assump_19
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p2 p3 p7 p4 p1 p6 p5 : Prop)
theorem file4_84870 : (((((p4 ∧ p4) ∧ (p5 ∨ p6)) ∨ ((p1 ∧ p7) ∧ (p2 → False))) → (((p3 ∧ p4) ∧ (True → False)) → ((True → p5) → False))) ∨ ((((p6 → False) → (True → True)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_1
      case inl assump_16 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            cases assump_19
            case inl assump_26 =>
              have assump_63 : True := by
                apply True.intro
              let assump_33 := assump_7 assump_63
              apply False.elim assump_33
            case inr assump_27 =>
              have assump_64 : True := by
                apply True.intro
              let assump_42 := assump_7 assump_64
              apply False.elim assump_42
      case inr assump_17 =>
        cases assump_17
        case intro assump_46 assump_47 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            have assump_65 : True := by
              apply True.intro
            let assump_59 := assump_7 assump_65
            apply False.elim assump_59


variable (p5 p2 p3 p1 p6 p7 p4 : Prop)
theorem file4_86215 : (((((p3 ∨ p4) ∨ (p7 → False)) → ((True ∨ p2) ∨ (p5 → p6))) → (((p1 → False) ∧ (True ∧ p3)) ∨ ((p6 ∨ p2) → False))) → ((((p5 → False) → (False ∨ True)) ∨ ((p4 → p3) ∨ (True ∧ p3))) ∨ (((p7 ∨ p3) → False) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply Or.inr
  apply True.intro


variable (p2 p4 p1 p5 p7 p3 p0 p6 : Prop)
theorem file4_86599 : (((((p2 → p4) → (p6 → p4)) → ((p1 ∧ True) ∨ (False → False))) ∨ (((p2 ∧ True) ∨ (False → p7)) ∨ ((False ∨ p4) ∧ (False → False)))) ∨ ((((False → p2) ∨ (p4 → p6)) → ((False → p1) → (p1 ∧ True))) → (((p4 → False) ∨ (p3 → p5)) ∨ ((p2 ∧ p2) ∨ (p0 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  apply False.elim assump_4


variable (p4 p3 p1 p6 p5 p7 p2 : Prop)
theorem file4_87031 : (((((p5 ∧ p3) ∧ (p7 → False)) ∧ ((p1 ∨ p3) → (p6 → p6))) ∨ (((p5 ∧ False) → False) ∨ ((p1 → False) ∨ (p4 → p2)))) ∨ ((((p7 → False) → (p5 → False)) → ((p5 ∨ p3) → False)) → False)) := by
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    apply False.elim assump_21


variable (p5 p0 p4 p7 p6 : Prop)
theorem file4_87423 : ((((((p6 → p0) → (p4 → p5)) ∧ ((p4 → p7) ∧ (p7 → False))) → (((False ∨ False) → False) → ((False ∧ p6) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p6 → p0) → (p4 → p5)) ∧ ((p4 → p7) ∧ (p7 → False))) → (((False ∨ False) → False) → ((False ∧ p6) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p2 p7 p6 : Prop)
theorem file4_87978 : (((((p4 ∧ p6) → (p7 ∨ p2)) → ((p7 → p2) → (p6 ∨ True))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p4 ∧ p6) → (p7 ∨ p2)) → ((p7 → p2) → (p6 ∨ True))) := by
    intro assump_5
    intro assump_6
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p0 p3 p4 p5 p6 p7 : Prop)
theorem file4_88355 : (((((p3 → False) ∨ (p6 → p0)) → ((p5 → p3) ∧ (True → p7))) → False) → ((((p6 → False) ∧ (p6 ∧ False)) → False) ∨ (((p0 → False) ∧ (p0 ∧ p4)) → ((p5 ∧ False) → (p3 ∧ False))))) := by
  intro assump_33
  apply Or.inl
  intro assump_36
  cases assump_36
  case intro assump_37 assump_38 =>
    cases assump_38
    case intro assump_41 assump_42 =>
      apply False.elim assump_42


variable (p7 p5 p4 p3 p2 p0 : Prop)
theorem file4_88793 : (((((p0 → p5) ∨ (True → False)) ∧ ((p3 ∨ p0) ∨ (p4 → p0))) ∧ (((p2 ∨ True) ∨ (True ∨ p3)) → ((False → p0) → (p5 → False)))) → ((((p5 ∧ p7) → (p2 → p2)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case inl assump_13 =>
          cases assump_13
          case inl assump_15 =>
            have assump_147 : ((p5 ∧ p7) → (p2 → p2)) := by
              intro assump_30
              intro assump_31
              cases assump_30
              case intro assump_34 assump_35 =>
                exact assump_31
            let assump_29 := assump_2 assump_147
            apply False.elim assump_29
          case inr assump_16 =>
            have assump_148 : ((p5 ∧ p7) → (p2 → p2)) := by
              intro assump_57
              intro assump_58
              cases assump_57
              case intro assump_61 assump_62 =>
                exact assump_58
            let assump_56 := assump_2 assump_148
            apply False.elim assump_56
        case inr assump_14 =>
          have assump_149 : ((p5 ∧ p7) → (p2 → p2)) := by
            intro assump_83
            intro assump_84
            cases assump_83
            case intro assump_87 assump_88 =>
              exact assump_84
          let assump_82 := assump_2 assump_149
          apply False.elim assump_82
      case inr assump_10 =>
        cases assump_8
        case inl assump_98 =>
          cases assump_98
          case inl assump_100 =>
            have assump_150 : True := by
              apply True.intro
            let assump_113 := assump_10 assump_150
            apply False.elim assump_113
          case inr assump_101 =>
            have assump_151 : True := by
              apply True.intro
            let assump_128 := assump_10 assump_151
            apply False.elim assump_128
        case inr assump_99 =>
          have assump_152 : True := by
            apply True.intro
          let assump_143 := assump_10 assump_152
          apply False.elim assump_143


variable (p3 p7 p0 p4 : Prop)
theorem file4_91007 : (((((False ∧ p4) ∧ (p7 ∨ p7)) → ((p0 ∧ True) → (True → p3))) → False) → False) := by
  intro assump_1
  have assump_25 : (((False ∧ p4) ∧ (p7 ∨ p7)) → ((p0 ∧ True) → (True → p3))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_5
      case intro assump_16 assump_17 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p1 p0 p4 p3 p2 p6 p5 : Prop)
theorem file4_91599 : (((((p3 → False) ∨ (p0 ∧ p4)) → ((p1 → False) → (p5 → p5))) ∨ (((p2 → False) ∨ (True ∨ p0)) ∧ ((p4 ∨ p2) ∨ (False ∧ True)))) ∨ ((((p0 → False) ∨ (p0 → False)) → False) ∨ (((p1 → p6) → False) → ((False → p6) → (p0 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    exact assump_3
  case inr assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      exact assump_3


variable (p1 p3 : Prop)
theorem file4_92120 : (((((p3 ∨ p1) ∧ (p1 → p3)) → False) ∧ (((True → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_19 : ((True → False) → False) := by
      intro assump_9
      have assump_20 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_20
      apply False.elim assump_12
    let assump_8 := assump_3 assump_19
    apply False.elim assump_8


variable (p4 p7 p1 p0 p6 p2 p3 p5 : Prop)
theorem file4_92619 : ((((((p4 → False) ∧ (p3 ∨ p2)) ∨ ((p6 ∧ p1) ∧ (p7 ∧ p1))) ∨ (((p6 → True) → False) ∨ ((p3 → False) ∧ (p2 → False)))) ∧ ((((p7 → False) → False) → ((p7 ∨ p1) ∨ (p3 ∧ p2))) ∧ (((p6 ∧ False) ∧ (p7 → False)) ∧ ((p0 → p5) → False)))) → False) := by
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
          case inl assump_12 =>
            cases assump_3
            case intro assump_16 assump_17 =>
              cases assump_17
              case intro assump_20 assump_21 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  cases assump_22
                  case intro assump_24 assump_25 =>
                    apply False.elim assump_25
          case inr assump_13 =>
            cases assump_3
            case intro assump_32 assump_33 =>
              cases assump_33
              case intro assump_36 assump_37 =>
                cases assump_36
                case intro assump_38 assump_39 =>
                  cases assump_38
                  case intro assump_40 assump_41 =>
                    apply False.elim assump_41
      case inr assump_7 =>
        cases assump_7
        case intro assump_46 assump_47 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            cases assump_47
            case intro assump_54 assump_55 =>
              cases assump_3
              case intro assump_60 assump_61 =>
                cases assump_61
                case intro assump_64 assump_65 =>
                  cases assump_64
                  case intro assump_66 assump_67 =>
                    cases assump_66
                    case intro assump_68 assump_69 =>
                      apply False.elim assump_69
    case inr assump_5 =>
      cases assump_5
      case inl assump_74 =>
        cases assump_3
        case intro assump_78 assump_79 =>
          cases assump_79
          case intro assump_82 assump_83 =>
            cases assump_82
            case intro assump_84 assump_85 =>
              cases assump_84
              case intro assump_86 assump_87 =>
                apply False.elim assump_87
      case inr assump_75 =>
        cases assump_75
        case intro assump_92 assump_93 =>
          cases assump_3
          case intro assump_98 assump_99 =>
            cases assump_99
            case intro assump_102 assump_103 =>
              cases assump_102
              case intro assump_104 assump_105 =>
                cases assump_104
                case intro assump_106 assump_107 =>
                  apply False.elim assump_107


variable (p6 p1 p7 p5 : Prop)
theorem file4_95436 : (((((False → False) → False) → ((True ∧ p1) → False)) → (((False ∧ False) ∧ (p6 ∨ p6)) → False)) ∨ ((((p7 ∧ p7) → (p5 → False)) ∧ ((False ∧ p5) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5


variable (p1 p4 p7 p3 : Prop)
theorem file4_95847 : (((((p4 ∨ True) ∨ (True → False)) ∨ ((p1 ∧ p7) → (p7 → p3))) → False) → False) := by
  intro assump_1
  have assump_8 : (((p4 ∨ True) ∨ (True → False)) ∨ ((p1 ∧ p7) → (p7 → p3))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p6 p0 p4 p7 p5 p1 p3 : Prop)
theorem file4_96231 : (((((p3 → False) → False) → False) → (((False ∧ True) → False) ∨ ((p3 ∧ True) → False))) ∧ ((((True → False) → (p5 → p1)) ∨ ((p7 → False) → (p5 ∧ p1))) ∨ (((p6 ∧ p6) → (p4 → False)) ∧ ((p0 → p1) → (p5 → False))))) := by
  apply And.intro
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5
  apply Or.inl
  apply Or.inl
  intro assump_9
  intro assump_10
  have assump_19 : True := by
    apply True.intro
  let assump_15 := assump_9 assump_19
  apply False.elim assump_15


variable (p7 p5 p0 : Prop)
theorem file4_96833 : ((((((False → False) ∨ (p0 ∨ p7)) → ((True → False) ∧ (p5 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False → False) ∨ (p0 ∨ p7)) → ((True → False) ∧ (p5 → False))) → False) := by
    intro assump_5
    have assump_21 : ((False → False) ∨ (p0 ∨ p7)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_21
    let assump_12 := And.left assump_8
    have assump_22 : True := by
      apply True.intro
    let assump_13 := assump_12 assump_22
    apply False.elim assump_13
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p1 p2 p6 p7 p5 p3 p4 : Prop)
theorem file4_97534 : (((((p7 ∧ p5) → False) ∨ ((p3 ∧ p4) ∧ (False → False))) → (((p1 ∨ p2) → (False → True)) ∨ ((p5 → p6) ∧ (True ∨ True)))) ∨ ((((True → p5) ∧ (p2 ∧ p3)) ∧ ((p7 ∨ p5) → False)) ∨ (((p4 → True) → (p5 → False)) ∧ ((p1 ∧ p7) ∧ (p7 ∧ p5))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        apply Or.inl
        intro assump_18
        intro assump_19
        apply True.intro


variable (p5 p6 p0 p1 p3 p7 p2 : Prop)
theorem file4_98218 : (((((False → p3) ∨ (p3 ∨ False)) ∨ ((p6 → False) ∨ (p1 ∧ p0))) ∨ (((p0 ∧ p5) ∨ (p7 → p7)) ∨ ((p5 ∧ True) → (p5 → p6)))) ∨ ((((p2 → p1) → (p6 → True)) → ((p7 ∨ False) ∧ (p3 ∧ p2))) ∧ (((p6 → False) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply False.elim assump_1


variable (p5 p6 p4 p3 p2 p0 p7 : Prop)
theorem file4_98609 : (((((p3 ∧ p0) ∨ (p4 → False)) ∨ ((p6 → p7) → False)) → (((p6 ∧ p0) → False) → ((False ∧ p5) → False))) → ((((p7 → False) → (False → False)) ∨ ((False → False) → False)) ∨ (((p0 → p5) → False) ∧ ((p5 ∨ p2) ∨ (p0 ∧ p6))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p2 p4 p7 p0 p1 p5 p3 : Prop)
theorem file4_99008 : (((((p0 → p5) ∨ (p2 → False)) ∧ ((False → True) ∨ (p7 ∨ p0))) → (((p4 ∨ False) ∧ (p7 → p0)) → ((True → False) → False))) ∨ ((((p5 → False) → False) ∨ ((p7 ∨ p7) ∧ (p5 → p4))) ∧ (((p1 ∧ False) ∧ (p5 → False)) → ((False ∧ True) ∧ (p5 ∧ p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          cases assump_15
          case inl assump_20 =>
            have assump_95 : True := by
              apply True.intro
            let assump_28 := assump_3 assump_95
            apply False.elim assump_28
          case inr assump_21 =>
            cases assump_21
            case inl assump_32 =>
              have assump_96 : True := by
                apply True.intro
              let assump_41 := assump_3 assump_96
              apply False.elim assump_41
            case inr assump_33 =>
              have assump_97 : True := by
                apply True.intro
              let assump_52 := assump_3 assump_97
              apply False.elim assump_52
        case inr assump_17 =>
          cases assump_15
          case inl assump_58 =>
            have assump_98 : True := by
              apply True.intro
            let assump_66 := assump_3 assump_98
            apply False.elim assump_66
          case inr assump_59 =>
            cases assump_59
            case inl assump_70 =>
              have assump_99 : True := by
                apply True.intro
              let assump_79 := assump_3 assump_99
              apply False.elim assump_79
            case inr assump_71 =>
              have assump_100 : True := by
                apply True.intro
              let assump_89 := assump_3 assump_100
              apply False.elim assump_89
    case inr assump_9 =>
      apply False.elim assump_9


variable (p5 p0 p3 p6 p2 p4 p7 p1 : Prop)
theorem file4_101039 : (((((p5 → False) → False) ∨ ((p1 ∨ p7) → False)) ∨ (((p3 → False) → False) → False)) → ((((p4 ∧ p0) ∨ (p4 → True)) ∨ ((p1 → False) → False)) ∨ (((False ∧ p3) → (p6 → p2)) → ((p3 ∨ p6) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      intro assump_8
      apply True.intro
    case inr assump_5 =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      intro assump_11
      apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_14
    apply True.intro


variable (p0 p7 p4 p1 p2 : Prop)
theorem file4_101742 : (((((False → False) → False) ∧ ((p2 → p7) ∨ (p1 → False))) → False) ∨ ((((True → False) → False) → ((p4 → p7) ∨ (p7 → False))) → (((p0 ∨ False) → False) ∨ ((p7 → True) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_28 : (False → False) := by
        intro assump_12
        apply False.elim assump_12
      let assump_11 := assump_2 assump_28
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_29 : (False → False) := by
        intro assump_22
        apply False.elim assump_22
      let assump_21 := assump_2 assump_29
      apply False.elim assump_21


variable (p4 p3 p0 p2 p1 p5 p6 : Prop)
theorem file4_102501 : (((((False → False) ∨ (False ∧ p6)) → False) → (((p0 → p1) ∧ (p0 ∧ p5)) ∧ ((False → False) ∨ (p5 → False)))) → ((((p5 ∧ p3) ∨ (p6 → True)) ∧ ((True ∧ p1) ∧ (p4 ∧ p0))) → (((True ∨ p3) ∨ (p0 → False)) ∨ ((p2 ∨ p3) ∨ (p0 → False))))) := by
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_8
        case intro assump_17 assump_18 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            cases assump_18
            case intro assump_25 assump_26 =>
              apply Or.inl
              apply Or.inl
              apply Or.inl
              apply True.intro
    case inr assump_10 =>
      cases assump_8
      case intro assump_35 assump_36 =>
        cases assump_35
        case intro assump_37 assump_38 =>
          cases assump_36
          case intro assump_43 assump_44 =>
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply True.intro


variable (p6 p0 : Prop)
theorem file4_103625 : ((((((p0 → False) → (p6 ∨ True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p0 → False) → (p6 ∨ True)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p0 → False) → (p6 ∨ True)) := by
      intro assump_9
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p0 p7 p2 p5 p6 p1 : Prop)
theorem file4_104126 : ((((((p3 ∧ False) ∨ (False ∧ p1)) → False) → (((p3 ∧ p5) → (p2 → False)) ∧ ((p0 → p0) → False))) ∧ ((((p0 ∧ p2) → (p7 → p0)) ∧ ((p1 → p5) → False)) ∧ (((p2 ∨ p5) ∨ (p1 ∨ p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_29 : (p1 → p5) := by
          intro assump_18
          have assump_30 : ((p2 ∨ p5) ∨ (p1 ∨ p6)) := by
            apply Or.inr
            apply Or.inl
            exact assump_18
          let assump_22 := assump_7 assump_30
          apply False.elim assump_22
        let assump_17 := assump_9 assump_29
        apply False.elim assump_17


variable (p5 p1 p3 p4 p0 p6 p2 p7 : Prop)
theorem file4_104939 : (((((p3 ∧ True) ∨ (p4 ∧ p7)) ∧ ((p3 → p4) ∧ (False → p2))) → False) → ((((p7 ∧ p4) → (p0 → False)) → False) → (((p6 → False) → False) → ((p5 → False) → (p1 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  have assump_44 : ((p7 ∧ p4) → (p0 → False)) := by
    intro assump_18
    intro assump_19
    cases assump_18
    case intro assump_22 assump_23 =>
      have assump_45 : (((p3 ∧ True) ∨ (p4 ∧ p7)) ∧ ((p3 → p4) ∧ (False → p2))) := by
        apply And.intro
        apply Or.inr
        apply And.intro
        exact assump_23
        exact assump_22
        apply And.intro
        intro assump_32
        exact assump_23
        intro assump_35
        apply False.elim assump_35
      let assump_31 := assump_1 assump_45
      apply False.elim assump_31
  let assump_17 := assump_2 assump_44
  apply False.elim assump_17


variable (p0 p6 p7 p3 p5 p2 p4 : Prop)
theorem file4_105888 : (((((p4 → p4) ∨ (p0 ∧ p6)) ∧ ((p7 ∨ p0) ∨ (p0 ∧ p5))) ∧ (((False ∧ True) → False) → False)) → ((((p4 → p2) ∧ (p6 ∧ p7)) ∨ ((False → p4) ∧ (p3 → True))) → (((p5 → False) ∨ (True → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_1
          case intro assump_20 assump_21 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              cases assump_22
              case inl assump_24 =>
                cases assump_23
                case inl assump_28 =>
                  cases assump_28
                  case inl assump_30 =>
                    have assump_478 : ((False ∧ True) → False) := by
                      intro assump_37
                      cases assump_37
                      case intro assump_38 assump_39 =>
                        apply False.elim assump_38
                    let assump_36 := assump_21 assump_478
                    apply False.elim assump_36
                  case inr assump_31 =>
                    have assump_479 : ((False ∧ True) → False) := by
                      intro assump_50
                      cases assump_50
                      case intro assump_51 assump_52 =>
                        apply False.elim assump_51
                    let assump_49 := assump_21 assump_479
                    apply False.elim assump_49
                case inr assump_29 =>
                  cases assump_29
                  case intro assump_58 assump_59 =>
                    have assump_480 : ((False ∧ True) → False) := by
                      intro assump_67
                      cases assump_67
                      case intro assump_68 assump_69 =>
                        apply False.elim assump_68
                    let assump_66 := assump_21 assump_480
                    apply False.elim assump_66
              case inr assump_25 =>
                cases assump_25
                case intro assump_75 assump_76 =>
                  cases assump_23
                  case inl assump_81 =>
                    cases assump_81
                    case inl assump_83 =>
                      have assump_481 : ((False ∧ True) → False) := by
                        intro assump_90
                        cases assump_90
                        case intro assump_91 assump_92 =>
                          apply False.elim assump_91
                      let assump_89 := assump_21 assump_481
                      apply False.elim assump_89
                    case inr assump_84 =>
                      have assump_482 : ((False ∧ True) → False) := by
                        intro assump_103
                        cases assump_103
                        case intro assump_104 assump_105 =>
                          apply False.elim assump_104
                      let assump_102 := assump_21 assump_482
                      apply False.elim assump_102
                  case inr assump_82 =>
                    cases assump_82
                    case intro assump_111 assump_112 =>
                      have assump_483 : ((False ∧ True) → False) := by
                        intro assump_120
                        cases assump_120
                        case intro assump_121 assump_122 =>
                          apply False.elim assump_121
                      let assump_119 := assump_21 assump_483
                      apply False.elim assump_119
    case inr assump_9 =>
      cases assump_9
      case intro assump_128 assump_129 =>
        cases assump_1
        case intro assump_134 assump_135 =>
          cases assump_134
          case intro assump_136 assump_137 =>
            cases assump_136
            case inl assump_138 =>
              cases assump_137
              case inl assump_142 =>
                cases assump_142
                case inl assump_144 =>
                  have assump_484 : ((False ∧ True) → False) := by
                    intro assump_151
                    cases assump_151
                    case intro assump_152 assump_153 =>
                      apply False.elim assump_152
                  let assump_150 := assump_135 assump_484
                  apply False.elim assump_150
                case inr assump_145 =>
                  have assump_485 : ((False ∧ True) → False) := by
                    intro assump_164
                    cases assump_164
                    case intro assump_165 assump_166 =>
                      apply False.elim assump_165
                  let assump_163 := assump_135 assump_485
                  apply False.elim assump_163
              case inr assump_143 =>
                cases assump_143
                case intro assump_172 assump_173 =>
                  have assump_486 : ((False ∧ True) → False) := by
                    intro assump_181
                    cases assump_181
                    case intro assump_182 assump_183 =>
                      apply False.elim assump_182
                  let assump_180 := assump_135 assump_486
                  apply False.elim assump_180
            case inr assump_139 =>
              cases assump_139
              case intro assump_189 assump_190 =>
                cases assump_137
                case inl assump_195 =>
                  cases assump_195
                  case inl assump_197 =>
                    have assump_487 : ((False ∧ True) → False) := by
                      intro assump_204
                      cases assump_204
                      case intro assump_205 assump_206 =>
                        apply False.elim assump_205
                    let assump_203 := assump_135 assump_487
                    apply False.elim assump_203
                  case inr assump_198 =>
                    have assump_488 : ((False ∧ True) → False) := by
                      intro assump_217
                      cases assump_217
                      case intro assump_218 assump_219 =>
                        apply False.elim assump_218
                    let assump_216 := assump_135 assump_488
                    apply False.elim assump_216
                case inr assump_196 =>
                  cases assump_196
                  case intro assump_225 assump_226 =>
                    have assump_489 : ((False ∧ True) → False) := by
                      intro assump_234
                      cases assump_234
                      case intro assump_235 assump_236 =>
                        apply False.elim assump_235
                    let assump_233 := assump_135 assump_489
                    apply False.elim assump_233
  case inr assump_5 =>
    cases assump_2
    case inl assump_244 =>
      cases assump_244
      case intro assump_246 assump_247 =>
        cases assump_247
        case intro assump_250 assump_251 =>
          cases assump_1
          case intro assump_256 assump_257 =>
            cases assump_256
            case intro assump_258 assump_259 =>
              cases assump_258
              case inl assump_260 =>
                cases assump_259
                case inl assump_264 =>
                  cases assump_264
                  case inl assump_266 =>
                    have assump_490 : ((False ∧ True) → False) := by
                      intro assump_273
                      cases assump_273
                      case intro assump_274 assump_275 =>
                        apply False.elim assump_274
                    let assump_272 := assump_257 assump_490
                    apply False.elim assump_272
                  case inr assump_267 =>
                    have assump_491 : ((False ∧ True) → False) := by
                      intro assump_286
                      cases assump_286
                      case intro assump_287 assump_288 =>
                        apply False.elim assump_287
                    let assump_285 := assump_257 assump_491
                    apply False.elim assump_285
                case inr assump_265 =>
                  cases assump_265
                  case intro assump_294 assump_295 =>
                    have assump_492 : ((False ∧ True) → False) := by
                      intro assump_303
                      cases assump_303
                      case intro assump_304 assump_305 =>
                        apply False.elim assump_304
                    let assump_302 := assump_257 assump_492
                    apply False.elim assump_302
              case inr assump_261 =>
                cases assump_261
                case intro assump_311 assump_312 =>
                  cases assump_259
                  case inl assump_317 =>
                    cases assump_317
                    case inl assump_319 =>
                      have assump_493 : ((False ∧ True) → False) := by
                        intro assump_326
                        cases assump_326
                        case intro assump_327 assump_328 =>
                          apply False.elim assump_327
                      let assump_325 := assump_257 assump_493
                      apply False.elim assump_325
                    case inr assump_320 =>
                      have assump_494 : ((False ∧ True) → False) := by
                        intro assump_339
                        cases assump_339
                        case intro assump_340 assump_341 =>
                          apply False.elim assump_340
                      let assump_338 := assump_257 assump_494
                      apply False.elim assump_338
                  case inr assump_318 =>
                    cases assump_318
                    case intro assump_347 assump_348 =>
                      have assump_495 : ((False ∧ True) → False) := by
                        intro assump_356
                        cases assump_356
                        case intro assump_357 assump_358 =>
                          apply False.elim assump_357
                      let assump_355 := assump_257 assump_495
                      apply False.elim assump_355
    case inr assump_245 =>
      cases assump_245
      case intro assump_364 assump_365 =>
        cases assump_1
        case intro assump_370 assump_371 =>
          cases assump_370
          case intro assump_372 assump_373 =>
            cases assump_372
            case inl assump_374 =>
              cases assump_373
              case inl assump_378 =>
                cases assump_378
                case inl assump_380 =>
                  have assump_496 : ((False ∧ True) → False) := by
                    intro assump_387
                    cases assump_387
                    case intro assump_388 assump_389 =>
                      apply False.elim assump_388
                  let assump_386 := assump_371 assump_496
                  apply False.elim assump_386
                case inr assump_381 =>
                  have assump_497 : ((False ∧ True) → False) := by
                    intro assump_400
                    cases assump_400
                    case intro assump_401 assump_402 =>
                      apply False.elim assump_401
                  let assump_399 := assump_371 assump_497
                  apply False.elim assump_399
              case inr assump_379 =>
                cases assump_379
                case intro assump_408 assump_409 =>
                  have assump_498 : ((False ∧ True) → False) := by
                    intro assump_417
                    cases assump_417
                    case intro assump_418 assump_419 =>
                      apply False.elim assump_418
                  let assump_416 := assump_371 assump_498
                  apply False.elim assump_416
            case inr assump_375 =>
              cases assump_375
              case intro assump_425 assump_426 =>
                cases assump_373
                case inl assump_431 =>
                  cases assump_431
                  case inl assump_433 =>
                    have assump_499 : ((False ∧ True) → False) := by
                      intro assump_440
                      cases assump_440
                      case intro assump_441 assump_442 =>
                        apply False.elim assump_441
                    let assump_439 := assump_371 assump_499
                    apply False.elim assump_439
                  case inr assump_434 =>
                    have assump_500 : ((False ∧ True) → False) := by
                      intro assump_453
                      cases assump_453
                      case intro assump_454 assump_455 =>
                        apply False.elim assump_454
                    let assump_452 := assump_371 assump_500
                    apply False.elim assump_452
                case inr assump_432 =>
                  cases assump_432
                  case intro assump_461 assump_462 =>
                    have assump_501 : ((False ∧ True) → False) := by
                      intro assump_470
                      cases assump_470
                      case intro assump_471 assump_472 =>
                        apply False.elim assump_471
                    let assump_469 := assump_371 assump_501
                    apply False.elim assump_469


variable (p3 p7 p5 : Prop)
theorem file4_119339 : (((((p5 ∨ True) → (p7 → False)) ∧ ((p3 ∨ True) ∨ (p3 → p7))) ∧ (((True → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_57 : ((True → False) → False) := by
            intro assump_17
            have assump_58 : True := by
              apply True.intro
            let assump_20 := assump_17 assump_58
            apply False.elim assump_20
          let assump_16 := assump_3 assump_57
          apply False.elim assump_16
        case inr assump_11 =>
          have assump_59 : ((True → False) → False) := by
            intro assump_32
            have assump_60 : True := by
              apply True.intro
            let assump_35 := assump_32 assump_60
            apply False.elim assump_35
          let assump_31 := assump_3 assump_59
          apply False.elim assump_31
      case inr assump_9 =>
        have assump_61 : ((True → False) → False) := by
          intro assump_47
          have assump_62 : True := by
            apply True.intro
          let assump_50 := assump_47 assump_62
          apply False.elim assump_50
        let assump_46 := assump_3 assump_61
        apply False.elim assump_46


variable (p7 p6 p0 p2 p3 p5 p1 p4 : Prop)
theorem file4_120768 : (((((p5 → p5) → False) → False) ∨ (((False → p2) ∧ (p6 ∨ p1)) ∧ ((p1 ∧ False) → False))) ∨ ((((True ∨ False) ∧ (p4 ∧ p7)) → ((p3 ∧ p6) ∨ (p4 ∨ p0))) ∧ (((p3 ∨ p2) → False) → ((False → p0) ∨ (p6 → p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (p5 → p5) := by
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p7 p2 p4 p1 p3 p0 : Prop)
theorem file4_121226 : (((((p0 ∧ p6) ∧ (p0 → p1)) ∨ ((p3 → p1) → False)) ∨ (((p6 → True) ∧ (False ∨ False)) → ((False ∨ p6) ∧ (False ∧ p7)))) → ((((False → p7) → False) → False) ∨ (((p2 ∨ True) ∨ (p6 ∧ False)) ∨ ((p4 → p4) ∧ (p3 ∧ False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply Or.inl
          intro assump_16
          have assump_50 : (False → p7) := by
            intro assump_20
            apply False.elim assump_20
          let assump_19 := assump_16 assump_50
          apply False.elim assump_19
    case inr assump_5 =>
      apply Or.inl
      intro assump_28
      have assump_51 : (False → p7) := by
        intro assump_32
        apply False.elim assump_32
      let assump_31 := assump_28 assump_51
      apply False.elim assump_31
  case inr assump_3 =>
    apply Or.inl
    intro assump_40
    have assump_52 : (False → p7) := by
      intro assump_44
      apply False.elim assump_44
    let assump_43 := assump_40 assump_52
    apply False.elim assump_43


