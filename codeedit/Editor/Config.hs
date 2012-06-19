{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS -fno-warn-missing-signatures #-}

module Editor.Config where

import qualified Graphics.DrawingCombinators as Draw
import qualified Graphics.UI.Bottle.EventMap as E

mk = E.ModKey

noMods = mk E.noMods
ctrl = mk E.ctrl . E.charKey
alt = mk E.alt . E.charKey
shift = mk E.shift . E.charKey
ctrlAlt = mk (E.noMods {E.modCtrl = True, E.modAlt = True}) . E.charKey
-- altShift = mk E.noMods { E.modAlt = True, E.modShift = True } . E.charKey
k = noMods . E.charKey

quitKeys          = [ctrl 'q']
undoKeys          = [ctrl 'z']
redoKeys          = [ctrl 'y']
makeBranchKeys    = [ctrl 's']

jumpToBranchesKeys = [mk E.ctrl E.KeyF10]

overlayDocKeys    = [noMods E.KeyF1, alt 'h']

addNextParamKeys  = [E.ModKey E.noMods E.KeySpace]

delBranchKeys     = [alt 'o']

closePaneKeys     = [alt 'w']
movePaneDownKeys  = [mk E.alt E.KeyDown]
movePaneUpKeys    = [mk E.alt E.KeyUp]

replaceKeys       = [alt 'r']

pickResultKeys    = [noMods E.KeyEnter]
jumpToDefinitionKeys  = [noMods E.KeyEnter]
delKeys           = [noMods E.KeyBackspace, noMods E.KeyDel, mk E.alt E.KeyDel]
giveAsArgumentKeys = [k ']', shift '0']
callWithArgumentKeys = [k '[', shift '9']
addNextArgumentKeys = [E.ModKey E.noMods E.KeySpace]
debugModeKeys = [ctrlAlt 'd']

newDefinitionKeys = [alt 'n']

definitionColor = Draw.Color 0.8 0.5 1 1
parameterColor = Draw.Color 0.2 0.8 0.9 1

literalIntColor = Draw.Color 0 1 0 1

previousCursorKeys = [mk E.alt E.KeyLeft]

focusedHoleBackgroundColor = Draw.Color 1 0 0 0.361
unfocusedHoleBackgroundColor = Draw.Color 1 0 0 1

unfocusedReadOnlyHoleBackgroundColor = Draw.Color 0.7 0.3 0.3 1

parenHighlightColor = Draw.Color 0.3 0 1 0.25

jumpToLhsKeys = [k '`']
jumpToRhsKeys = [k '=', noMods E.KeyPadEqual]

lambdaWrapKeys = [k '\\']
addWhereItemKeys = [k 'w']

lambdaColor = Draw.Color 1 0.2 0.2 1
lambdaTextSize = 30

rightArrowColor = Draw.Color 1 0.2 0.2 1
rightArrowTextSize = 30

whereColor = Draw.Color 0.8 0.6 0.1 1
whereTextSize = 16
whereScaleFactor = 0.85

foldKeys = [k '-']
unfoldKeys = foldKeys

helpTextSize = 10
baseTextSize = 25

typeErrorBackgroundColor = Draw.Color 0.5 0.05 0.05 1

typeScaleFactor = 0.4
squareParensScaleFactor = 0.96

foreignModuleColor = Draw.Color 1 0.3 0.35 1
foreignVarColor = Draw.Color 1 0.65 0.25 1

cutKeys = [ctrl 'x', k 'x']
pasteKeys = [ctrl 'v', k 'v']

inactiveTintColor = Draw.Color 1 1 1 0.8
activeDefBGColor = Draw.Color 0 0 0.2 1
