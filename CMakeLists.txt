add_cirkit_library(
  NAME cirkit_mign_sat
  AUTO_DIRS src
  USE
	cirkit_mign
  INCLUDE
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/src
  DEFINE
    PUBLIC ADDON_MIGN_SAT
  COMMANDS
    classical/cli/commands/mign_sat_commands.hpp
  OPTIONS
    PRIVATE -Wno-sign-compare
)
