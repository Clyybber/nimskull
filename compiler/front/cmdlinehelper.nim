#
#
#           The Nim Compiler
#        (c) Copyright 2018 Nim contributors
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## Helpers for binaries that use compiler passes, e.g.: nim, nimsuggest, nimfix

import
  std/[
    os
  ],
  ast/[
    idents,
    reports
  ],
  modules/[
    modulegraphs
  ],
  front/[
    nimconf,
    commands,
    msgs,
    options,
    condsyms
  ],
  utils/[
    pathutils
  ],
  backend/[
    extccomp
  ]


proc prependCurDir*(f: AbsoluteFile): AbsoluteFile =
  when defined(unix):
    if os.isAbsolute(f.string): result = f
    else: result = AbsoluteFile("./" & f.string)
  else:
    result = f

type
  NimProg* = ref object
    suggestMode*: bool
    supportsStdinFile*: bool
    processCmdLine*: proc(pass: TCmdLinePass, cmd: string; config: ConfigRef)

proc initDefinesProg*(self: NimProg, conf: ConfigRef, name: string) =
  condsyms.initDefines(conf.symbols)
  defineSymbol conf, name

proc processCmdLineAndProjectPath*(self: NimProg, conf: ConfigRef, cmd: string = "") =
  self.processCmdLine(passCmd1, cmd, conf)
  if conf.projectIsCmd and conf.projectName in ["-", ""]:
    handleCmdInput(conf)
  elif self.supportsStdinFile and conf.projectName == "-":
    handleStdinInput(conf)
  elif conf.projectName != "":
    setFromProjectName(conf, conf.projectName)
  else:
    conf.projectPath = AbsoluteDir canonicalizePath(conf, AbsoluteFile getCurrentDir())

proc loadConfigsAndProcessCmdLine*(self: NimProg, cache: IdentCache; conf: ConfigRef;
                                   graph: ModuleGraph): bool =
  ## Load all the necessary configuration files and command-line options.
  ## Main entry point for configuration processing.
  if self.suggestMode:
    conf.setCmd cmdIdeTools
  if conf.cmd == cmdNimscript:
    incl(conf, optWasNimscript)

  loadConfigs(DefaultConfig, cache, conf, graph.idgen) # load all config files

  if not self.suggestMode:
    let scriptFile = conf.projectFull.changeFileExt("nims")
    # 'nim foo.nims' means to just run the NimScript file and do nothing more:
    if fileExists(scriptFile) and scriptFile == conf.projectFull:
      if conf.cmd == cmdNone: conf.setCmd cmdNimscript
      if conf.cmd == cmdNimscript: return false
  # now process command line arguments again, because some options in the
  # command line can overwrite the config file's settings
  extccomp.initVars(conf)
  self.processCmdLine(passCmd2, "", conf)
  if conf.cmd == cmdNone:
    localReport(conf, ExternalReport(kind: rextCommandMissing))

  graph.suggestMode = self.suggestMode
  return true

proc loadConfigsAndRunMainCommand*(
    self: NimProg, cache: IdentCache; conf: ConfigRef; graph: ModuleGraph): bool =

  ## Alias for loadConfigsAndProcessCmdLine, here for backwards compatibility
  loadConfigsAndProcessCmdLine(self, cache, conf, graph)
