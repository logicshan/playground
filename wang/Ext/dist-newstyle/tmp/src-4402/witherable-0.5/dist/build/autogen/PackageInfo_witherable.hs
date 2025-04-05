{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module PackageInfo_witherable (
    name,
    version,
    synopsis,
    copyright,
    homepage,
  ) where

import Data.Version (Version(..))
import Prelude

name :: String
name = "witherable"
version :: Version
version = Version [0,5] []

synopsis :: String
synopsis = "filterable traversable"
copyright :: String
copyright = "Copyright (c) 2014 Fumiaki Kinoshita"
homepage :: String
homepage = "https://github.com/fumieval/witherable"
