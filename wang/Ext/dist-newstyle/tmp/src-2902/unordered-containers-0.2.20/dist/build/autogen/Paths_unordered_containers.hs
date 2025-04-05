{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
#if __GLASGOW_HASKELL__ >= 810
{-# OPTIONS_GHC -Wno-prepositive-qualified-module #-}
#endif
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_unordered_containers (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where


import qualified Control.Exception as Exception
import qualified Data.List as List
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude


#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,2,20] []

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath




bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "/home/sn/.cabal/store/ghc-9.4.8/unordered-containers-0.2.20-8379bca1d848435b46c694ebeb135b98b20c684d124fed4e6d8c37085800cb03/bin"
libdir     = "/home/sn/.cabal/store/ghc-9.4.8/unordered-containers-0.2.20-8379bca1d848435b46c694ebeb135b98b20c684d124fed4e6d8c37085800cb03/lib"
dynlibdir  = "/home/sn/.cabal/store/ghc-9.4.8/unordered-containers-0.2.20-8379bca1d848435b46c694ebeb135b98b20c684d124fed4e6d8c37085800cb03/lib"
datadir    = "/home/sn/.cabal/store/ghc-9.4.8/unordered-containers-0.2.20-8379bca1d848435b46c694ebeb135b98b20c684d124fed4e6d8c37085800cb03/share"
libexecdir = "/home/sn/.cabal/store/ghc-9.4.8/unordered-containers-0.2.20-8379bca1d848435b46c694ebeb135b98b20c684d124fed4e6d8c37085800cb03/libexec"
sysconfdir = "/home/sn/.cabal/store/ghc-9.4.8/unordered-containers-0.2.20-8379bca1d848435b46c694ebeb135b98b20c684d124fed4e6d8c37085800cb03/etc"

getBinDir     = catchIO (getEnv "unordered_containers_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "unordered_containers_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "unordered_containers_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "unordered_containers_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "unordered_containers_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "unordered_containers_sysconfdir") (\_ -> return sysconfdir)



joinFileName :: String -> String -> FilePath
joinFileName ""  fname = fname
joinFileName "." fname = fname
joinFileName dir ""    = dir
joinFileName dir fname
  | isPathSeparator (List.last dir) = dir ++ fname
  | otherwise                       = dir ++ pathSeparator : fname

pathSeparator :: Char
pathSeparator = '/'

isPathSeparator :: Char -> Bool
isPathSeparator c = c == '/'
