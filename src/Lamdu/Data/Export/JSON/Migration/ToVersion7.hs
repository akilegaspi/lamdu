module Lamdu.Data.Export.JSON.Migration.ToVersion7 (migrate) where

import qualified Control.Lens as Lens
import qualified Data.Aeson as Aeson
import           Data.Aeson.Lens (_Object, _String)
import qualified Data.Vector as Vector
import           Lamdu.Data.Export.JSON.Migration.Common (migrateToVer)

import           Lamdu.Prelude

migrateVal :: Aeson.Value -> Either Text (Maybe Aeson.Value)
migrateVal val =
    case val ^? _Object . Lens.ix "nomType" . _String of
    Just x
        | x == "OpaqueNominal" -> Right Nothing
        | otherwise -> Left ("Unexpected nomType: " <> x)
    _ -> Right (Just val)

migrate :: Aeson.Value -> Either Text Aeson.Value
migrate =
    migrateToVer 7
    (traverse migrateVal <&> Lens._Right %~ Vector.fromList . (^.. Lens.folded . Lens.folded))
