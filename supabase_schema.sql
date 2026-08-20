-- supabase_schema.sql
-- TopRate Supabase schema. Keep this in the repo as the authoritative record
-- of the database structure - the free tier has NO backups, so if the project
-- is ever lost, running this recreates the tables, then the load scripts
-- repopulate them from the CSVs.
--
-- Table: wpr_form_history
--   One row per (run_id, date): each run_id is a horse's form-capture event
--   that dumps one row per historical race date. Composite primary key on
--   (run_id, date). Loaded from wpr_form_history.csv.gz via
--   load_form_history_to_supabase.py (upsert on the composite key).

create table if not exists wpr_form_history (
  run_id            bigint,
  horse_id          bigint,
  horse             text,
  scrape_date       text,
  formnumber        integer,
  racenumber        integer,
  date              text,
  track             text,
  trackcode         text,
  trackgrading      double precision,
  distance          integer,
  going             text,
  wpr               double precision,
  weightcarried     double precision,
  barrier           integer,
  pricestarting     double precision,
  positionsettled   double precision,
  position800m      double precision,
  position600m      double precision,
  position400m      double precision,
  position200m      double precision,
  positionfinish    double precision,
  margin800m        double precision,
  margin600m        double precision,
  margin400m        double precision,
  margin200m        double precision,
  marginfinish      double precision,
  raceshapeearly    double precision,
  raceshapemid      double precision,
  raceshapelate     double precision,
  winner            text,
  isbarriertrial    boolean,
  sect_i_time       double precision,
  sect_ld_early     double precision,
  sect_i_early      double precision,
  sect_i_to600      double precision,
  sect_i_to800      double precision,
  sect_i_l200       double precision,
  sect_i_l400       double precision,
  sect_i_l600       double precision,
  sect_i_l800       double precision,
  sect_i_400_200    double precision,
  sect_i_600_400    double precision,
  sect_i_800_400    double precision,
  sect_i_800_600    double precision,
  field_size        double precision,
  weight_handicap   double precision,
  race_class        text,
  is_letup          boolean,
  is_spell          boolean,
  race_id           double precision,
  meeting_id        double precision,
  blinkers_on       boolean,
  gear_changes      text,
  comments_steward  text,
  comments_video    text,
  time_last600m     double precision,
  jockey            text,
  trainer           text,
  is_jumpout        boolean,
  primary key (run_id, date)
);

-- Helpful indexes for the queries the dashboard / analysis will run.
-- (Add these once; they speed up date-range and per-horse lookups.)
create index if not exists idx_wfh_date     on wpr_form_history (date);
create index if not exists idx_wfh_horse_id on wpr_form_history (horse_id);
create index if not exists idx_wfh_race_id  on wpr_form_history (race_id);
